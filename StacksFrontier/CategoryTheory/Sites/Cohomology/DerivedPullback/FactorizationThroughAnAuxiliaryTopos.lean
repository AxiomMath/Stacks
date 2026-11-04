module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Factoring the module pullback through the auxiliary ringed topos `X'`

Let `f : (Sh(C'), O') ⟶ (Sh(C), O)` be a morphism of ringed topoi presented by a continuous
functor `f.u` between the underlying sites.  This file factors `f` as

`X --h--> X' --g--> Y`,  where  `X' = (X.C, X.J, f⁻¹ O_Y)`,

with `g` carrying the whole geometric content (`g.u = f.u`, structure map the adjunction unit)
and `h` carrying the whole ring-theoretic content (`h.u = 𝟭`, structure map `f⁻¹ O_Y ⟶ O_X`).
On sheaves of modules this gives `f^* ≅ g^* ⋙ h^*`, where `g^*` is the inverse image with no
change of rings and `h^*` is extension of scalars along `f⁻¹ O_Y ⟶ O_X`.

## Main definitions

* `StacksPullbackFactorization.invRing`: `f⁻¹ O_Y`, as a sheaf of commutative rings on `X`.
* `StacksPullbackFactorization.auxTopos`: the auxiliary ringed topos `X' = (X.C, X.J, f⁻¹ O_Y)`.
* `StacksPullbackFactorization.auxHomG`: `g : X' ⟶ Y`, with `g.u = f.u` and structure map the
  unit of the inverse-image/direct-image adjunction on sheaves of commutative rings.
* `StacksPullbackFactorization.auxHomH`: `h : X ⟶ X'`, with `h.u = 𝟭` and structure map the
  adjoint `f⁻¹ O_Y ⟶ O_X` of `f^♯`.

## Main results

* `StacksPullbackFactorization.fSharp_comp` and `fSharpRing_comp`: the structure maps of `g`
  and `h` compose to that of `f`.
* `StacksPullbackFactorization.pushforwardFactorIso`: `f_* ≅ h_* ⋙ g_*`.
* `StacksPullbackFactorization.pullbackFactorIso`: `f^* ≅ g^* ⋙ h^*`.
* `StacksPullbackFactorization.pullbackTopos_auxHomH`: `h^*` is the extension of scalars
  `Stacks.Sheaves.ModuleAdjunction.extendScalars` along `f⁻¹ O_Y ⟶ O_X`.

## Implementation notes

**Pushforward along the identity functor is the identity on the nose.**  Both
`((𝟭 X.C).sheafPushforwardContinuous CommRingCat.{u} X.J X.J).obj X.O = X.O` and its
`RingCat` analogue hold by `rfl`, so `h`'s structure map needs no comparison isomorphism and
`Functor.sheafPushforwardContinuousId` never appears.  Likewise
`(auxHomG f).u ⋙ (auxHomH f).u = f.u` holds by `rfl`, so no index transport on the underlying
functor is required: no proof term in this file contains a coercion along an equality of
functors, and none of the comparison isomorphisms of the identity pushforward appears.

**The factorization is built on the pushforward side and transported.**
`SheafOfModules.pushforwardComp` is `Iso.refl`, so the composite pushforward *is* the
pushforward of the composite structure map; `SheafOfModules.pushforwardCongr` then moves it
along `fSharpRing_comp`.  The pullback statement follows by uniqueness of left adjoints
rather than by any computation with pullbacks.

**Universes.**  Both ringed topoi are at `RingedTopos.{u, u, u}`, as required by
`SheafOfModules.pullback`, which needs both sites small in the universe of the sections, and by
`CategoryTheory.Functor.IsMorphismOfSites`, which is stated for small categories `{C D : Type u}`.

`f⁻¹` on sheaves of commutative rings uses sheafification of presheaves of commutative rings,
`AlgebraicGeometry.SheafOfModules.hasSheafify_commRingCat`, together with
`AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat` for
the left adjoint; their `UnivLE` side conditions are all `UnivLE.{u, u}` here.

## References

* [The Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [The Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace StacksPullbackFactorization

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}

/-- `f⁻¹ O_Y`, the inverse image of the structure sheaf of `Y`, as a sheaf of commutative
rings on the site of `X`. -/
abbrev invRing (f : AlgebraicGeometry.RingedToposSiteHom X Y) : Sheaf X.J CommRingCat.{u} :=
  (f.u.sheafPullback CommRingCat.{u} Y.J X.J).obj Y.O

/-- The auxiliary ringed topos `X' = (X.C, X.J, f⁻¹ O_Y)`: the site of `X` with the inverse
image of the structure sheaf of `Y` as its structure sheaf. -/
abbrev auxTopos (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    AlgebraicGeometry.RingedTopos.{u, u, u} :=
  { C := X.C, J := X.J, O := invRing f }

/-- `g : X' ⟶ Y`, the geometric half of the factorization: the same underlying continuous
functor as `f`, with structure map the unit of the inverse-image/direct-image adjunction. -/
def auxHomG (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    AlgebraicGeometry.RingedToposSiteHom (auxTopos f) Y where
  u := f.u
  isContinuous := f.isContinuous
  fSharp := (f.u.sheafAdjunctionContinuous CommRingCat.{u} Y.J X.J).unit.app Y.O

/-- `h : X ⟶ X'`, the ring-theoretic half of the factorization: the identity on the underlying
site, with structure map the adjoint `f⁻¹ O_Y ⟶ O_X` of `f^♯`. -/
def auxHomH (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    AlgebraicGeometry.RingedToposSiteHom X (auxTopos f) where
  u := 𝟭 X.C
  fSharp :=
    ((f.u.sheafAdjunctionContinuous CommRingCat.{u} Y.J X.J).homEquiv Y.O X.O).symm f.fSharp

/-- The structure maps of `g` and `h` compose to that of `f`. -/
theorem fSharp_comp (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    (auxHomG f).fSharp ≫ (f.u.sheafPushforwardContinuous CommRingCat.{u} Y.J X.J).map
      (auxHomH f).fSharp = f.fSharp :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

section Ring

variable [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- `fSharp_comp` after forgetting commutativity: the structure maps of `g` and `h`, read as
maps of sheaves of not necessarily commutative rings, compose to that of `f`. -/
theorem fSharpRing_comp (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    (auxHomG f).fSharpRing ≫ (f.u.sheafPushforwardContinuous RingCat.{u} Y.J X.J).map
      (auxHomH f).fSharpRing = f.fSharpRing := by
  have h := fSharp_comp f
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  exact congrArg (fun (t : Y.O ⟶ _) =>
    (forget₂ CommRingCat.{u} RingCat.{u}).map (t.hom.app U)) h

/-- **`f_* ≅ h_* ⋙ g_*`.**  The direct image of sheaves of modules along `f` is the composite
of those along `h` and `g`. -/
def pushforwardFactorIso (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    (auxHomH f).pushforwardTopos ⋙ (auxHomG f).pushforwardTopos ≅ f.pushforwardTopos :=
  haveI : ((auxHomG f).u ⋙ (auxHomH f).u).IsContinuous Y.J X.J :=
    Functor.isContinuous_comp f.u (𝟭 X.C) Y.J X.J X.J
  SheafOfModules.pushforwardComp (auxHomG f).fSharpRing (auxHomH f).fSharpRing ≪≫
    SheafOfModules.pushforwardCongr (fSharpRing_comp f)

section Pullback

variable [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **`f^* ≅ g^* ⋙ h^*`.**  The pullback of sheaves of modules along `f` factors as the
inverse image with no change of rings, followed by extension of scalars along
`f⁻¹ O_Y ⟶ O_X`. -/
def pullbackFactorIso (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    (auxHomG f).pullbackTopos ⋙ (auxHomH f).pullbackTopos ≅ f.pullbackTopos :=
  Adjunction.leftAdjointUniq
    (((auxHomG f).pullbackPushforwardAdjunctionTopos.comp
      (auxHomH f).pullbackPushforwardAdjunctionTopos).ofNatIsoRight (pushforwardFactorIso f))
    f.pullbackPushforwardAdjunctionTopos

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The pullback `h^*` along `h : X ⟶ X'` is, definitionally, the extension of scalars
`Stacks.Sheaves.ModuleAdjunction.extendScalars` along `f⁻¹ O_Y ⟶ O_X`. -/
theorem pullbackTopos_auxHomH (f : AlgebraicGeometry.RingedToposSiteHom X Y) :
    (auxHomH f).pullbackTopos
      = Stacks.Sheaves.ModuleAdjunction.extendScalars ((auxHomH f).fSharpRing) :=
  rfl

end Pullback

end Ring

end StacksPullbackFactorization
