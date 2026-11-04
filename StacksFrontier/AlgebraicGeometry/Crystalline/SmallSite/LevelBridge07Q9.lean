module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalConnected
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechLocal07Q9

/-!
# Morphisms into the objects of the chaotic subsite, read on rings

Fix a global crystalline situation with `X` and `S` affine and `p` nilpotent on `Γ(X, ⊤)`.  The
chaotic subsite `𝒞` of thickenings of the whole of `X` is anti-equivalent to the little affine
crystalline category `Cris(Γ(X, ⊤)/Γ(S, ⊤))`, by
`Crystalline.GlobalCrystallineSituation.wholeSiteEquivLittleAffine`.  This file extends the
dictionary to morphisms *out of an arbitrary object* `B` of the big crystalline category
`CRIS(X/S)` with affine thickened scheme — `B` need not lie over the whole of `X`, nor even be an
object of the small site — *into* the object of `𝒞` attached to an object `L` of
`Cris(Γ(X, ⊤)/Γ(S, ⊤))`: such morphisms are the morphisms `L ⟶ Γ(B)` of the big affine category
`CRIS(Γ(X, ⊤)/Γ(S, ⊤))`.

## Main definitions

* `levelBridge` — the map `(B ⟶ L^♭) → (L ⟶ Γ(B))`, where `L^♭` is the object of `𝒞` attached
  to `L`.

## Main results

* `levelBridge_injective` and `exists_levelBridge_eq` — it is a bijection.
* `levelBridge_comp` and `levelBridge_comp_inverse_map` — it turns precomposition into
  postcomposition with the map on global sections, and postcomposition with the image of a
  morphism `L' ⟶ L` into precomposition with it.

## References

* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline

variable {R : GlobalCrystallineSituation.{u}} [IsAffine R.X] [IsAffine R.S.scheme]
  (hp : IsNilpotent (R.p : Γ(R.X, ⊤)))

/-- The object of `CRIS(X/S)` attached to an object of `Cris(Γ(X, ⊤)/Γ(S, ⊤))` by the inverse of
`wholeSiteEquivLittleAffine`. -/
abbrev inverseThickening (L : _root_.Crystalline.CrystallineThickening.{u, u, u}
    (affineSituation R hp)) : Thickening R :=
  (wholeToBig R).obj ((wholeSiteEquivLittleAffine hp).inverse.obj L).unop

/-- The structure morphism to `X` of `inverseThickening hp L` is an isomorphism. -/
instance isIso_inverseThickening_toX
    (L : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation R hp)) :
    IsIso (inverseThickening hp L).toX :=
  ((wholeSiteEquivLittleAffine hp).inverse.obj L).unop.property

/-- **A morphism of `CRIS(X/S)` into the object attached to `L`, read on rings**: the morphism
`L ⟶ Γ(B)` of `CRIS(Γ(X, ⊤)/Γ(S, ⊤))` it induces on global sections, preceded by the counit of
the equivalence. -/
def levelBridge (B : Thickening R) [IsAffine B.thickening.source]
    (L : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation R hp))
    (k : B ⟶ inverseThickening hp L) : L.obj ⟶ wholeThickeningToAffine hp B :=
  ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L).hom ≫ wholeHomToAffine hp k

variable {hp}

/-- `levelBridge` turns precomposition into postcomposition with the map on global sections. -/
theorem levelBridge_comp {B B' : Thickening R} [IsAffine B.thickening.source]
    [IsAffine B'.thickening.source]
    {L : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation R hp)}
    (m : B' ⟶ B) (k : B ⟶ inverseThickening hp L) :
    levelBridge hp B' L (m ≫ k) = levelBridge hp B L k ≫ wholeHomToAffine hp m :=
  (congrArg (((wholeSiteEquivLittleAffine hp).counitIso.inv.app L).hom ≫ ·)
    (wholeHomToAffine_comp hp m k)).trans (Category.assoc _ _ _).symm

/-- `levelBridge` turns postcomposition with the image of `ψ : L' ⟶ L` into precomposition with
`ψ`. -/
theorem levelBridge_comp_inverse_map {B : Thickening R} [IsAffine B.thickening.source]
    {L L' : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation R hp)}
    (k : B ⟶ inverseThickening hp L) (ψ : L' ⟶ L) :
    levelBridge hp B L'
        (k ≫ (wholeToBig R).map ((wholeSiteEquivLittleAffine hp).inverse.map ψ).unop) =
      ψ.hom ≫ levelBridge hp B L k := by
  have hn : ψ.hom ≫ ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L).hom =
      ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L').hom ≫
        ((wholeSiteEquivLittleAffine hp).functor.map
          ((wholeSiteEquivLittleAffine hp).inverse.map ψ)).hom :=
    congrArg (fun x ↦ x.hom) ((wholeSiteEquivLittleAffine hp).counitIso.inv.naturality ψ)
  calc levelBridge hp B L'
        (k ≫ (wholeToBig R).map ((wholeSiteEquivLittleAffine hp).inverse.map ψ).unop)
      = ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L').hom ≫
          (((wholeSiteEquivLittleAffine hp).functor.map
            ((wholeSiteEquivLittleAffine hp).inverse.map ψ)).hom ≫ wholeHomToAffine hp k) :=
        congrArg (((wholeSiteEquivLittleAffine hp).counitIso.inv.app L').hom ≫ ·)
          (wholeHomToAffine_comp hp k _)
    _ = (((wholeSiteEquivLittleAffine hp).counitIso.inv.app L').hom ≫
          ((wholeSiteEquivLittleAffine hp).functor.map
            ((wholeSiteEquivLittleAffine hp).inverse.map ψ)).hom) ≫ wholeHomToAffine hp k :=
        (Category.assoc _ _ _).symm
    _ = (ψ.hom ≫ ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L).hom) ≫
          wholeHomToAffine hp k := congrArg (· ≫ wholeHomToAffine hp k) hn.symm
    _ = ψ.hom ≫ levelBridge hp B L k := Category.assoc _ _ _

/-- **`levelBridge` is injective**: a morphism into an object of `𝒞` is determined by the
morphism it induces on global sections (`wholeHomToAffine_injective`). -/
theorem levelBridge_injective (B : Thickening R) [IsAffine B.thickening.source]
    (L : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation R hp)) :
    Function.Injective (levelBridge hp B L) := by
  intro k k' h
  refine wholeHomToAffine_injective hp ?_
  have : IsIso ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L).hom :=
    (affineIsCrystalline hp).ι.map_isIso _
  exact (cancel_epi ((wholeSiteEquivLittleAffine hp).counitIso.inv.app L).hom).mp h

/-- **`levelBridge` is surjective**: every morphism `L ⟶ Γ(B)` is induced by a morphism into the
object of `𝒞` attached to `L`, namely `Spec` of a morphism `L ⟶ Γ(B)` (`homOfAffineHom`) followed
by `specIsoInverseObj`. -/
theorem exists_levelBridge_eq (B : Thickening R) [IsAffine B.thickening.source]
    (L : _root_.Crystalline.CrystallineThickening.{u, u, u} (affineSituation R hp))
    (φ : L.obj ⟶ wholeThickeningToAffine hp B) :
    ∃ k : B ⟶ inverseThickening hp L, levelBridge hp B L k = φ := by
  have : IsIso (specThickeningOfAffine hp L.obj).toX := isIso_specToX hp L.obj L.property
  have : IsAffine (specThickeningOfAffine hp L.obj).thickening.source :=
    IsAffine.of_isIso (specThickeningOfAffine hp L.obj).toX
  let m : specThickeningOfAffine hp L.obj ⟶ inverseThickening hp L :=
    (wholeToBig R).map (specIsoInverseObj hp L).inv
  let jIso : L.obj ≅ L.obj :=
    ((affineIsCrystalline hp).ι.mapIso ((wholeSiteEquivLittleAffine hp).counitIso.app L)).symm ≪≫
      (wholeSiteToAffine hp).mapIso (specIsoInverseObj hp L).op.symm ≪≫
        wholeThickeningToAffineSpecIso hp L.obj
  have hj : levelBridge hp (specThickeningOfAffine hp L.obj) L m ≫
      (wholeThickeningToAffineSpecIso hp L.obj).hom = jIso.hom := rfl
  refine ⟨homOfAffineHom hp B L.obj (jIso.inv ≫ φ) L.property ≫ m, ?_⟩
  refine (levelBridge_comp _ _).trans ?_
  rw [wholeHomToAffine_homOfAffineHom]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jIso.inv ≫ φ) hj).trans
    (jIso.hom_inv_id_assoc φ))

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
