module

public import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import Mathlib.RingTheory.Etale.Weakly
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.RingTheory.Flat.Localization
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.StrictHenselization
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Existence
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.Descent
public import StacksFrontier.RingTheory.WeaklyEtale.StrictlyHenselian
public import StacksCore.Tactic.StacksAttribute

/-!
# Weakly étale morphisms and local rings

A morphism of schemes is weakly étale if and only if the induced map on local rings at every
point is weakly étale. Equivalently, it is weakly étale exactly when, at every point, the map
of local rings induces an isomorphism between compatible strict henselizations.

## Main results

* `AlgebraicGeometry.weaklyEtale_iff_stalkMap_weaklyEtale` characterizes weakly étale morphisms
  by their maps on stalks.
* `AlgebraicGeometry.weaklyEtale_iff_strictHenselizationMap_bijective` characterizes weakly
  étale morphisms by their maps on strict henselizations of stalks.

## Implementation notes

The local ring map in the source is represented by `Scheme.Hom.stalkMap`. Its canonical algebra
structure is the one induced by that ring homomorphism.

A strict henselization of a local ring `R` is represented by a local `R`-algebra whose residue
field is a separable closure of the residue field of `R` and which satisfies
`IsLocalRing.IsHenselization`. The residue-field map `φ` records the compatible choices of
separable closures. The two displayed commutative squares characterize the map between strict
henselizations induced by `φ`; its existence and uniqueness are the functoriality of strict
henselization (Stacks Project, Tag 04GU). Thus quantifying over such a map makes the
characterization independent of all choices while retaining the canonical residue-field
compatibility. An isomorphism of rings is expressed by bijectivity of its ring homomorphism.

## References

* [Stacks Project, Tag 094Q](https://stacks.math.columbia.edu/tag/094Q)
* [Stacks Project, Tag 094Z](https://stacks.math.columbia.edu/tag/094Z)
* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private lemma stalkMap_eq_eqToHom_of_eq_id {X : AlgebraicGeometry.Scheme.{u}}
    (k : X ⟶ X) (h : k = 𝟙 X) (x : X) :
    k.stalkMap x =
      eqToHom (congrArg X.presheaf.stalk (congrArg (fun m : X ⟶ X => m x) h)) := by
  subst h
  rw [AlgebraicGeometry.Scheme.Hom.stalkMap_id, eqToHom_refl]
  rfl

private lemma stalkMap_comp_of_retraction
    {X Z : AlgebraicGeometry.Scheme.{u}} (i : X ⟶ Z) (p : Z ⟶ X)
    (h : i ≫ p = 𝟙 X) (x : X) : p.stalkMap (i x) ≫ i.stalkMap x =
      eqToHom (congrArg X.presheaf.stalk (congrArg (fun k : X ⟶ X => k x) h)) := by
  rw [← AlgebraicGeometry.Scheme.Hom.stalkMap_comp]
  exact stalkMap_eq_eqToHom_of_eq_id (i ≫ p) h x

private lemma tensorProduct_localization_of_eq
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (a b x : X) (ha : a = x) (hb : b = x) (hab : f a = f b)
    (C : CommRingCat.{u}) (p : X.presheaf.stalk a ⟶ C)
    (q : X.presheaf.stalk b ⟶ C) (d : C ⟶ X.presheaf.stalk x)
    (hp : p ≫ d = eqToHom (congrArg X.presheaf.stalk ha))
    (hq : q ≫ d = eqToHom (congrArg X.presheaf.stalk hb))
    (H : let := (f.stalkMap a).hom.toAlgebra
      let := ((eqToHom (congrArg Y.presheaf.stalk hab)) ≫ f.stalkMap b).hom.toAlgebra
      ∃ φ : TensorProduct (Y.presheaf.stalk (f a))
          (X.presheaf.stalk a) (X.presheaf.stalk b) →+* C,
        φ.comp Algebra.TensorProduct.includeLeftRingHom = p.hom ∧
        φ.comp Algebra.TensorProduct.includeRight.toRingHom = q.hom ∧
        let := φ.toAlgebra
        ∃ M : Submonoid (TensorProduct (Y.presheaf.stalk (f a))
          (X.presheaf.stalk a) (X.presheaf.stalk b)), IsLocalization M C) :
    let := (f.stalkMap x).hom.toAlgebra
    ∃ φ : TensorProduct (Y.presheaf.stalk (f x))
        (X.presheaf.stalk x) (X.presheaf.stalk x) →+* C,
      d.hom.comp φ = (Algebra.TensorProduct.lmul' (Y.presheaf.stalk (f x))
        (S := X.presheaf.stalk x)).toRingHom ∧
      let := φ.toAlgebra
      ∃ M : Submonoid (TensorProduct (Y.presheaf.stalk (f x))
        (X.presheaf.stalk x) (X.presheaf.stalk x)), IsLocalization M C := by
  subst a b
  simp only [eqToHom_refl] at H hp hq
  let := (f.stalkMap x).hom.toAlgebra
  obtain ⟨φ, hleft, hright, M, hM⟩ := H
  refine ⟨φ, ?_, M, hM⟩
  apply Algebra.TensorProduct.ringHom_ext
  · exact ((congrArg d.hom.comp hleft).trans (congrArg CommRingCat.Hom.hom hp)).trans
      (congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.lmul'_comp_includeLeft
        (R := Y.presheaf.stalk (f x)) (S := X.presheaf.stalk x))).symm
  · exact ((congrArg d.hom.comp hright).trans (congrArg CommRingCat.Hom.hom hq)).trans
      (congrArg AlgHom.toRingHom
      (Algebra.TensorProduct.lmul'_comp_includeRight
        (R := Y.presheaf.stalk (f x)) (S := X.presheaf.stalk x))).symm

private lemma flat_diagonal_stalk_iff_flat_lmul
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (x : X) :
    letI := (f.stalkMap x).hom.toAlgebra
    ((Limits.pullback.diagonal f).stalkMap x).hom.Flat ↔
      (Algebra.TensorProduct.lmul' (Y.presheaf.stalk (f x))
        (S := X.presheaf.stalk x)).Flat := by
  let := (f.stalkMap x).hom.toAlgebra
  have hfst : Limits.pullback.fst f f ((Limits.pullback.diagonal f) x) = x := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, Limits.pullback.diagonal_fst]
    rfl
  have hsnd : Limits.pullback.snd f f ((Limits.pullback.diagonal f) x) = x := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, Limits.pullback.diagonal_snd]
    rfl
  have hp : (Limits.pullback.fst f f).stalkMap ((Limits.pullback.diagonal f) x) ≫
      (Limits.pullback.diagonal f).stalkMap x =
        eqToHom (congrArg X.presheaf.stalk hfst) :=
    stalkMap_comp_of_retraction _ _ (Limits.pullback.diagonal_fst f) x
  have hq : (Limits.pullback.snd f f).stalkMap ((Limits.pullback.diagonal f) x) ≫
      (Limits.pullback.diagonal f).stalkMap x =
        eqToHom (congrArg X.presheaf.stalk hsnd) :=
    stalkMap_comp_of_retraction _ _ (Limits.pullback.diagonal_snd f) x
  obtain ⟨φ, hcomp, M, hM⟩ := tensorProduct_localization_of_eq f _ _ x hfst hsnd
    (congrArg (fun k : Limits.pullback f f ⟶ Y => k ((Limits.pullback.diagonal f) x))
      Limits.pullback.condition)
    _ _ _ ((Limits.pullback.diagonal f).stalkMap x) hp hq
    (BaseChangeStalk.pullback_stalk_isLocalization f f ((Limits.pullback.diagonal f) x))
  let : Algebra
      (TensorProduct (Y.presheaf.stalk (f x))
        (X.presheaf.stalk x) (X.presheaf.stalk x))
      ((Limits.pullback f f).presheaf.stalk ((Limits.pullback.diagonal f) x)) := φ.toAlgebra
  let : Algebra ((Limits.pullback f f).presheaf.stalk ((Limits.pullback.diagonal f) x))
      (X.presheaf.stalk x) := ((Limits.pullback.diagonal f).stalkMap x).hom.toAlgebra
  let : Algebra
      (TensorProduct (Y.presheaf.stalk (f x))
        (X.presheaf.stalk x) (X.presheaf.stalk x))
      (X.presheaf.stalk x) :=
    (Algebra.TensorProduct.lmul' (Y.presheaf.stalk (f x))
      (S := X.presheaf.stalk x)).toRingHom.toAlgebra
  have : IsScalarTower
      (TensorProduct (Y.presheaf.stalk (f x))
        (X.presheaf.stalk x) (X.presheaf.stalk x))
      ((Limits.pullback f f).presheaf.stalk ((Limits.pullback.diagonal f) x))
      (X.presheaf.stalk x) := by
    apply IsScalarTower.of_algebraMap_eq'
    simpa only [RingHom.algebraMap_toAlgebra] using hcomp.symm
  change Module.Flat ((Limits.pullback f f).presheaf.stalk ((Limits.pullback.diagonal f) x))
      (X.presheaf.stalk x) ↔
    Module.Flat (TensorProduct (Y.presheaf.stalk (f x))
      (X.presheaf.stalk x) (X.presheaf.stalk x)) (X.presheaf.stalk x)
  have := hM
  exact (flat_iff_flat_localization M _ (X.presheaf.stalk x)).symm

/-- A morphism of schemes is weakly étale if and only if all of its maps on local rings
are weakly étale. -/
@[stacks 094Q]
theorem weaklyEtale_iff_stalkMap_weaklyEtale
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    AlgebraicGeometry.WeaklyEtale f ↔
      ∀ x : X,
        letI := (f.stalkMap x).hom.toAlgebra
        Algebra.WeaklyEtale (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  rw [AlgebraicGeometry.weaklyEtale_iff]
  constructor
  · rintro ⟨hf, hd⟩ x
    let := (f.stalkMap x).hom.toAlgebra
    have : AlgebraicGeometry.Flat f := hf
    have : AlgebraicGeometry.Flat (Limits.pullback.diagonal f) := hd
    exact { flat := AlgebraicGeometry.Flat.stalkMap f x
            flat_lmul' := (flat_diagonal_stalk_iff_flat_lmul f x).mp
              (AlgebraicGeometry.Flat.stalkMap _ _) }
  · exact fun h ↦ ⟨AlgebraicGeometry.Flat.of_stalkMap _ fun x ↦ (h x).flat,
      AlgebraicGeometry.Flat.of_stalkMap _ fun x ↦
        (flat_diagonal_stalk_iff_flat_lmul f x).mpr (h x).flat_lmul'⟩

/-- A henselization of a local ring is weakly étale over it. -/
private theorem weaklyEtale_of_isHenselization (R L Rh : Type u) [CommRing R] [IsLocalRing R]
    [Field L] [Algebra R L] [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [Algebra (IsLocalRing.ResidueField R) L] [IsLocalRing.IsHenselization R L Rh] :
    Algebra.WeaklyEtale R Rh :=
  Algebra.weaklyEtale_of_ind_etale (IsLocalRing.IsHenselization.ind_etale (L := L))

/-- If `f` is weakly étale, then every local map between strict henselizations of its local
rings at `x` that is compatible with the map of local rings is bijective. -/
private theorem bijective_strictHenselizationMap_of_weaklyEtale
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (hf : AlgebraicGeometry.WeaklyEtale f)
    (x : X) (Ysh Xsh : Type u)
    [CommRing Ysh] [IsLocalRing Ysh]
    [CommRing Xsh] [IsLocalRing Xsh]
    [Algebra (Y.presheaf.stalk (f x)) Ysh]
    [Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField Ysh)]
    [IsSepClosure (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField Ysh)]
    [IsLocalRing.IsHenselization (Y.presheaf.stalk (f x))
      (IsLocalRing.ResidueField Ysh) Ysh]
    [Algebra (X.presheaf.stalk x) Xsh]
    [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.ResidueField Xsh)]
    [IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.ResidueField Xsh)]
    [IsLocalRing.IsHenselization (X.presheaf.stalk x)
      (IsLocalRing.ResidueField Xsh) Xsh]
    (g : Ysh →+* Xsh) (hg : IsLocalHom g)
    (hcomm : g.comp (algebraMap (Y.presheaf.stalk (f x)) Ysh) =
      (algebraMap (X.presheaf.stalk x) Xsh).comp (f.stalkMap x).hom) :
    Function.Bijective g := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : Algebra.WeaklyEtale (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (weaklyEtale_iff_stalkMap_weaklyEtale f).mp hf x
  let : Algebra Ysh Xsh := g.toAlgebra
  have : IsLocalHom (algebraMap Ysh Xsh) := hg
  let : Algebra (Y.presheaf.stalk (f x)) Xsh :=
    ((algebraMap (X.presheaf.stalk x) Xsh).comp (f.stalkMap x).hom).toAlgebra
  have : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) Xsh :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (Y.presheaf.stalk (f x)) Ysh Xsh :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (DFunLike.congr_fun hcomm a).symm
  have : Algebra.WeaklyEtale (X.presheaf.stalk x) Xsh :=
    weaklyEtale_of_isHenselization _ (IsLocalRing.ResidueField Xsh) _
  have : HenselianLocalRing Ysh :=
    IsLocalRing.IsHenselization.henselian
      (R := Y.presheaf.stalk (f x)) (L := IsLocalRing.ResidueField Ysh)
  have : IsSepClosed (IsLocalRing.ResidueField Ysh) :=
    IsSepClosure.sep_closed (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
  exact bijective_algebraMap_of_weaklyEtale_of_isLocalHom Ysh Xsh
    (weaklyEtale_of_comp (Y.presheaf.stalk (f x)) Ysh Xsh
      (weaklyEtale_of_isHenselization _ (IsLocalRing.ResidueField Ysh) _)
      (Algebra.WeaklyEtale.trans (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) Xsh))

/-- Strict henselizations of the local rings of `f` at `x`, with residue fields compatible with
those of the local rings, admit a compatible local map between them. -/
private theorem exists_isLocalHom_strictHenselizationMap
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (x : X) (Ysh Xsh : Type u)
    [CommRing Ysh] [IsLocalRing Ysh]
    [CommRing Xsh] [IsLocalRing Xsh]
    [Algebra (Y.presheaf.stalk (f x)) Ysh]
    [Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField Ysh)]
    [IsSepClosure (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField Ysh)]
    [IsLocalRing.IsHenselization (Y.presheaf.stalk (f x))
      (IsLocalRing.ResidueField Ysh) Ysh]
    [Algebra (X.presheaf.stalk x) Xsh]
    [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.ResidueField Xsh)]
    [IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.ResidueField Xsh)]
    [IsLocalRing.IsHenselization (X.presheaf.stalk x)
      (IsLocalRing.ResidueField Xsh) Xsh]
    (hresY : ∀ a : Y.presheaf.stalk (f x),
      algebraMap (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
          (IsLocalRing.ResidueField Ysh) (IsLocalRing.residue _ a) =
        IsLocalRing.residue Ysh (algebraMap (Y.presheaf.stalk (f x)) Ysh a)) :
    ∃ (φ : IsLocalRing.ResidueField Ysh →+* IsLocalRing.ResidueField Xsh) (g : Ysh →+* Xsh),
      IsLocalHom g ∧
        g.comp (algebraMap (Y.presheaf.stalk (f x)) Ysh) =
          (algebraMap (X.presheaf.stalk x) Xsh).comp (f.stalkMap x).hom ∧
        (IsLocalRing.residue Xsh).comp g = φ.comp (IsLocalRing.residue Ysh) := by
  have : IsLocalHom (algebraMap (X.presheaf.stalk x) Xsh) :=
    IsLocalRing.IsHenselization.isLocalHom (L := IsLocalRing.ResidueField Xsh)
  let : Algebra (Y.presheaf.stalk (f x)) Xsh :=
    ((algebraMap (X.presheaf.stalk x) Xsh).comp (f.stalkMap x).hom).toAlgebra
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) Xsh) :=
    RingHom.isLocalHom_comp (algebraMap (X.presheaf.stalk x) Xsh) (f.stalkMap x).hom
  have : IsSepClosed (IsLocalRing.ResidueField Ysh) :=
    IsSepClosure.sep_closed (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
  have : IsSepClosed (IsLocalRing.ResidueField Xsh) :=
    IsSepClosure.sep_closed (IsLocalRing.ResidueField (X.presheaf.stalk x))
  have : HenselianLocalRing Xsh :=
    IsLocalRing.IsHenselization.henselian
      (R := X.presheaf.stalk x) (L := IsLocalRing.ResidueField Xsh)
  let : Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField Xsh) :=
    (IsLocalRing.ResidueField.map (algebraMap (Y.presheaf.stalk (f x)) Xsh)).toAlgebra
  let φ : IsLocalRing.ResidueField Ysh →ₐ[IsLocalRing.ResidueField (Y.presheaf.stalk (f x))]
      IsLocalRing.ResidueField Xsh := IsSepClosed.lift
  have hφ : φ.toRingHom.comp
        ((IsLocalRing.residue Ysh).comp (algebraMap (Y.presheaf.stalk (f x)) Ysh)) =
      (IsLocalRing.residue Xsh).comp (algebraMap (Y.presheaf.stalk (f x)) Xsh) := by
    ext a
    change φ (IsLocalRing.residue Ysh (algebraMap (Y.presheaf.stalk (f x)) Ysh a)) =
      IsLocalRing.residue Xsh (algebraMap (Y.presheaf.stalk (f x)) Xsh a)
    rw [← hresY a, φ.commutes]
    exact IsLocalRing.ResidueField.map_residue (algebraMap (Y.presheaf.stalk (f x)) Xsh) a
  obtain ⟨g, hg, hgres⟩ :=
    (StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale
      (IsLocalRing.IsHenselization.ind_etale
        (R := Y.presheaf.stalk (f x))
        (L := IsLocalRing.ResidueField Ysh) (Rh := Ysh)) φ.toRingHom hφ).exists
  exact ⟨φ.toRingHom, g.toRingHom, ⟨hg.map_nonunit⟩, RingHom.ext g.commutes, hgres⟩

/-- If a strict henselization of a local ring of `X` is faithfully flat over it, and a
compatible map from a strict henselization of the local ring of `Y` to it is bijective, then the
map of local rings is weakly étale. -/
private theorem weaklyEtale_stalkMap_of_bijective_strictHenselizationMap
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (x : X) (Ysh Xsh : Type u)
    [CommRing Ysh] [IsLocalRing Ysh]
    [CommRing Xsh] [IsLocalRing Xsh]
    [Algebra (Y.presheaf.stalk (f x)) Ysh]
    [Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField Ysh)]
    [IsLocalRing.IsHenselization (Y.presheaf.stalk (f x))
      (IsLocalRing.ResidueField Ysh) Ysh]
    [Algebra (X.presheaf.stalk x) Xsh]
    [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x))
      (IsLocalRing.ResidueField Xsh)]
    [IsLocalRing.IsHenselization (X.presheaf.stalk x)
      (IsLocalRing.ResidueField Xsh) Xsh]
    (g : Ysh →+* Xsh)
    (hcomm : g.comp (algebraMap (Y.presheaf.stalk (f x)) Ysh) =
      (algebraMap (X.presheaf.stalk x) Xsh).comp (f.stalkMap x).hom)
    (hg : Function.Bijective g) :
    letI := (f.stalkMap x).hom.toAlgebra
    Algebra.WeaklyEtale (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra (Y.presheaf.stalk (f x)) Xsh :=
    ((algebraMap (X.presheaf.stalk x) Xsh).comp (f.stalkMap x).hom).toAlgebra
  have : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) Xsh :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra Ysh Xsh := g.toAlgebra
  have : IsScalarTower (Y.presheaf.stalk (f x)) Ysh Xsh :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (DFunLike.congr_fun hcomm a).symm
  have : Algebra.Etale Ysh Xsh := (RingHom.Etale.of_bijective hg).toAlgebra
  have : Algebra.WeaklyEtale (Y.presheaf.stalk (f x)) Ysh :=
    weaklyEtale_of_isHenselization _ (IsLocalRing.ResidueField Ysh) _
  have : Module.FaithfullyFlat (X.presheaf.stalk x) Xsh :=
    IsLocalRing.IsHenselization.faithfullyFlat (L := IsLocalRing.ResidueField Xsh)
  exact (flat_lmul'_and_weaklyEtale_of_faithfullyFlat
    (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) Xsh).2
      (Algebra.WeaklyEtale.trans (Y.presheaf.stalk (f x)) Ysh Xsh)

/-- A morphism of schemes is weakly étale if and only if every map that it induces between
compatible strict henselizations of its local rings is an isomorphism. -/
@[stacks 094Z]
theorem weaklyEtale_iff_strictHenselizationMap_bijective
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    AlgebraicGeometry.WeaklyEtale f ↔
      ∀ (x : X) (Ysh Xsh : Type u)
        [CommRing Ysh] [IsLocalRing Ysh]
        [CommRing Xsh] [IsLocalRing Xsh]
        [Algebra (Y.presheaf.stalk (f x)) Ysh]
        [Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
          (IsLocalRing.ResidueField Ysh)]
        [IsSepClosure (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
          (IsLocalRing.ResidueField Ysh)]
        [IsLocalRing.IsHenselization (Y.presheaf.stalk (f x))
          (IsLocalRing.ResidueField Ysh) Ysh]
        [Algebra (X.presheaf.stalk x) Xsh]
        [Algebra (IsLocalRing.ResidueField (X.presheaf.stalk x))
          (IsLocalRing.ResidueField Xsh)]
        [IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x))
          (IsLocalRing.ResidueField Xsh)]
        [IsLocalRing.IsHenselization (X.presheaf.stalk x)
          (IsLocalRing.ResidueField Xsh) Xsh]
        (φ : IsLocalRing.ResidueField Ysh →+* IsLocalRing.ResidueField Xsh)
        (g : Ysh →+* Xsh),
        IsLocalHom g →
          g.comp (algebraMap (Y.presheaf.stalk (f x)) Ysh) =
            (algebraMap (X.presheaf.stalk x) Xsh).comp (f.stalkMap x).hom →
          (IsLocalRing.residue Xsh).comp g =
              φ.comp (IsLocalRing.residue Ysh) →
            Function.Bijective g := by
  constructor
  · intro hf x Ysh Xsh _ _ _ _ _ _ _ _ _ _ _ _ _ g hg hcomm _
    exact bijective_strictHenselizationMap_of_weaklyEtale f hf x Ysh Xsh g hg hcomm
  · intro h
    refine (weaklyEtale_iff_stalkMap_weaklyEtale f).mpr fun x ↦ ?_
    obtain ⟨Ysh, _, _, _, hYsh⟩ :=
      IsLocalRing.exists_isHenselization_separableClosure (Y.presheaf.stalk (f x))
    obtain ⟨Xsh, _, _, _, hXsh⟩ :=
      IsLocalRing.exists_isHenselization_separableClosure (X.presheaf.stalk x)
    obtain ⟨algResY, hYsh', hsepY, hresY⟩ :=
      IsLocalRing.IsHenselization.exists_residueFieldAlgebra
        (R := Y.presheaf.stalk (f x))
        (L := SeparableClosure (IsLocalRing.ResidueField (Y.presheaf.stalk (f x))))
        (Rh := Ysh)
    obtain ⟨algResX, hXsh', hsepX, -⟩ :=
      IsLocalRing.IsHenselization.exists_residueFieldAlgebra
        (R := X.presheaf.stalk x)
        (L := SeparableClosure (IsLocalRing.ResidueField (X.presheaf.stalk x)))
        (Rh := Xsh)
    have : IsSepClosure (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
        (IsLocalRing.ResidueField Ysh) := hsepY inferInstance
    have : IsSepClosure (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (IsLocalRing.ResidueField Xsh) := hsepX inferInstance
    obtain ⟨φ, g, hg, hcomm, hres⟩ := exists_isLocalHom_strictHenselizationMap f x Ysh Xsh hresY
    exact weaklyEtale_stalkMap_of_bijective_strictHenselizationMap f x Ysh Xsh g hcomm
      (h x Ysh Xsh φ g hg hcomm hres)

end AlgebraicGeometry
