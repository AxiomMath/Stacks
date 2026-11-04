module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModuleNatIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModulesCompIso
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Inverse images of modules along isomorphic functors, with scalars restricted

Given an isomorphism `ε : Φ ≅ Φ''` of inverse-image functors and a compatible morphism `β` of
pulled-back ring sheaves, the inverse-image functors on sheaves of modules, followed by restriction
of scalars along ring maps `a` and `b` with `a ≫ β = b`, are isomorphic.

## Main definitions

* `pullbackModuleRestrictScalarsIsoOfNatIso`: The isomorphism between
  `pullbackModuleFunctor J Φ O ⋙ restrictScalars a` and
  `pullbackModuleFunctor J Φ'' O ⋙ restrictScalars b`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

namespace Stacks.Sheaves.ToposPullback

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  {Φ Φ' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ']
  (O : Sheaf K RingCat.{ww'}) (e : Φ ⟶ Φ')

section Hom

variable (β : pullbackRingSheaf J Φ O ⟶ pullbackRingSheaf J Φ' O)
  (hβ : (sheafCompose J (forget RingCat.{ww})).map β = e.app (Sheaf.ringSheaf O))
  (G : SheafOfModules.{ww'} O)

include hβ

end Hom

section Iso

variable {Φ Φ'' : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)}
  [PreservesFiniteProducts Φ] [PreservesFiniteProducts Φ'']

/-- Given an isomorphism `ε : Φ ≅ Φ''` and a morphism `β` of pulled-back ring sheaves lying over
`ε` on the underlying sheaf of sets of `O`, and ring maps `a`, `b` with `a ≫ β = b`, the
isomorphism of functors between `pullbackModuleFunctor J Φ O ⋙ restrictScalars a` and
`pullbackModuleFunctor J Φ'' O ⋙ restrictScalars b`. -/
noncomputable def pullbackModuleRestrictScalarsIsoOfNatIso {R : Sheaf J RingCat.{ww}}
    (ε : Φ ≅ Φ'') (β : pullbackRingSheaf J Φ O ⟶ pullbackRingSheaf J Φ'' O)
    (hβ : (sheafCompose J (forget RingCat.{ww})).map β = ε.hom.app (Sheaf.ringSheaf O))
    (a : R ⟶ pullbackRingSheaf J Φ O) (b : R ⟶ pullbackRingSheaf J Φ'' O) (h : a ≫ β = b) :
    pullbackModuleFunctor J Φ O ⋙ SheafOfModules.restrictScalars a ≅
      pullbackModuleFunctor J Φ'' O ⋙ SheafOfModules.restrictScalars b :=
  have h1 : (pullbackModuleFunctor J Φ'' O ⋙ SheafOfModules.restrictScalars β) ⋙
        SheafOfModules.restrictScalars a =
      pullbackModuleFunctor J Φ'' O ⋙ SheafOfModules.restrictScalars (a ≫ β) := rfl
  have h2 : pullbackModuleFunctor J Φ'' O ⋙ SheafOfModules.restrictScalars (a ≫ β) =
      pullbackModuleFunctor J Φ'' O ⋙ SheafOfModules.restrictScalars b :=
    congrArg (fun c ↦ pullbackModuleFunctor J Φ'' O ⋙ SheafOfModules.restrictScalars c) h
  Functor.isoWhiskerRight (pullbackModuleFunctorIsoOfNatIso J O ε β hβ)
      (SheafOfModules.restrictScalars a) ≪≫ eqToIso (h1.trans h2)

end Iso

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.RingedToposHom

universe v u w v'' u'' w''

variable {X : RingedTopos.{v, u, w}} {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]

end AlgebraicGeometry.RingedToposHom

end
