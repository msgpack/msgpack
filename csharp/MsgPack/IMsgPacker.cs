using System;
using System.IO;

namespace MsgPack
{
    public interface IMsgPacker
    {
        #region Pack Generic
        byte[] Pack<T> (T o);
        void Pack<T> (Stream strm, T o);
        #endregion

        #region Pack
        byte[] Pack(object o);
        void Pack(Stream strm, object o);
        #endregion

        #region Unpack generic
        T Unpack<T> (byte[] buf);
        T Unpack<T> (byte[] buf, int offset, int size);
        T Unpack<T> (Stream strm);
        #endregion

        #region Unpack
        object Unpack (Type t, byte[] buf);
        object Unpack (Type t, byte[] buf, int offset, int size);
        object Unpack (Type t, Stream strm);
        #endregion
    }
}