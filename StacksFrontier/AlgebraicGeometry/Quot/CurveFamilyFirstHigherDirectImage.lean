module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomology
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstDirectImageBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Quot.ExtendsFibreIsoNearPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFlatStructureSheafPushforward

/-!
# Families of curves with `κ(s) = H⁰(X_s, 𝒪_{X_s})` (Stacks 0E1J)

Let `f : X → S` be a family of curves (Stacks 0D4Z) such that `κ(s) = H⁰(X_s, 𝒪_{X_s})` for every
point `s` of the base scheme `S`. Stacks 0E1J asserts:

1. `f_*𝒪_X = 𝒪_S`, and this holds universally;
2. `R¹f_*𝒪_X` is a finite locally free `𝒪_S`-module;
3. for every morphism `h : S' → S` with base change `f' : X' → S'`,
   `h^*(R¹f_*𝒪_X) = R¹f'_*𝒪_{X'}`.

## Main results

* `AlgebraicGeometry.Space.bijective_algebraMap_globalFunctions_relocalizeRestrict_of_field`:
  for a separated, flat, finitely presented algebraic space over a field `k` with `H⁰ = k`, the
  same holds after any base change `k → A'`.
* `AlgebraicGeometry.CurveFamily.bijective_algebraMap_globalFunctions_fibre_of_residueField`:
  the hypothesis of Stacks 0E1J at the residue fields gives `k = H⁰(X_k, 𝒪_{X_k})` at every
  field-valued point `Spec k → S`, the hypothesis of Stacks 0E6B.
* `AlgebraicGeometry.CurveFamily.isIso_structureSharp_and_baseChange_of_residueField`:
  **Stacks 0E1J, part (1).**
* `AlgebraicGeometry.CurveFamily.isFiniteLocallyFreeOnSite_firstDirectImage_of_residueField`:
  **Stacks 0E1J, part (2).**
* `AlgebraicGeometry.CurveFamily.isIso_firstDirectImageBaseChangeMap_of_residueField`:
  **Stacks 0E1J, part (3)**: the base change map `h^*(R¹f_*𝒪_X) ⟶ R¹f'_*𝒪_{X'}` is an
  isomorphism.

## Implementation notes

The hypothesis of the source, that `κ(s) → H⁰(X_s, 𝒪_{X_s})` is an isomorphism for every point
`s ∈ S` with `X_s = X ×_S Spec κ(s)`, is
`AlgebraicGeometry.CurveFamily.HasResidueFieldGlobalFunctions`.

"`f_*𝒪_X = 𝒪_S`" is that the structure map `f♯ : 𝒪_S ⟶ f_*𝒪_X` of Stacks 03G8 is an
isomorphism of sheaves of rings on the small étale site of `S`, and "universally" is that this
holds for the base change of `f` along every morphism `Y ⟶ S` from an algebraic space. "Finite
locally free" is Stacks 03DL (2) on the small étale site of `S`. In part (3), the morphisms
`h : S' → S` with their base changes are the morphisms of families of curves (Stacks 0D4Z),
whose squares are cartesian, and "`h^*(R¹f_*𝒪_X) = R¹f'_*𝒪_{X'}`" is that the base change map
`AlgebraicGeometry.CurveFamily.firstDirectImageBaseChangeMap` is an isomorphism.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u})

/-- **Global functions over a field commute with base change.** Let `X` be an algebraic space
over a field `k` whose structure morphism is separated, flat and of finite presentation, with
`k = H⁰(X, 𝒪_X)`. Then `A' = H⁰(X_{A'}, 𝒪)` for every `k`-algebra `A'` whose spectrum lies in
the site. -/
theorem bijective_algebraMap_globalFunctions_relocalizeRestrict_of_field {k : Type u} [Field k]
    {hk : B.Contains (Spec (.of k))} {X : (BigFppfOver B (Spec (.of k)) hk)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of k)) hk X) (f : X ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hk))))
    (hsep : IsSeparated B (Spec (.of k)) hk f) (hflat : IsFlat B (Spec (.of k)) hk f)
    (hfp : IsFinitePresentation B (Spec (.of k)) hk f)
    (h : Function.Bijective (algebraMap k (globalFunctions B (Spec (.of k)) hk X)))
    (A' : Type u) [CommRing A'] [Algebra k A'] (hA' : B.Contains (Spec (.of A')))
    (g : B.obj hA' ⟶ B.obj hk)
    (hg : B.inclusion.map g = Spec.map (CommRingCat.ofHom (algebraMap k A'))) :
    Function.Bijective (algebraMap A'
      (globalFunctions B (Spec (.of A')) hA' ((OverShriek.relocalizeRestrict g).obj X))) := by
  obtain ⟨W, R, p, r₁, r₂, hps, hpe, hR, hW, hRa, -, -, -, -⟩ :=
    exists_affine_atlas_flat_finitePresentation B hX f hsep hflat hfp
  let := siteObjectAlgebra B k W
  let := siteObjectAlgebra B k R
  refine (bijective_algebraMap_globalFunctions_relocalizeRestrict_iff B X hX p hps hpe r₁ r₂ hR
    hW hRa g hg).mpr ?_
  exact ((bijective_algebraMap_globalFunctions_iff B X hX p hps hpe r₁ r₂ hR).mp h).of_flat

variable {B} {S : Scheme.{u}} {hS : B.Contains S} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The fibre of `f` over a section depends on the section only through its equality class: a
section over `g` and the corresponding section over an equal `g'` have isomorphic fibres. -/
theorem nonempty_restrictedFibre_iso_of_eq (f : X ⟶ Y) {T : Scheme.{u}} (hT : B.Contains T)
    {g g' : B.obj hT ⟶ B.obj hS} (hg : g = g') (v : Y.obj (op (Over.mk g))) :
    Nonempty (restrictedFibre B S hS f hT g v ≅
      restrictedFibre B S hS f hT g' (Y.map (eqToHom (congrArg Over.mk hg.symm)).op v)) := by
  subst hg
  simp only [eqToHom_refl, op_id, Functor.map_id_apply]
  exact ⟨Iso.refl _⟩

end Space

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- The hypothesis of Stacks 0E1J at a point `s`, in the form of the fibre over the residue
field point: `κ(s) → H⁰(X_s, 𝒪_{X_s})` is bijective, with `X_s` the fibre of `f` over
`Spec κ(s) → S` formed over `κ(s)`. -/
theorem bijective_algebraMap_globalFunctions_residueFieldValuedPoint (X : CurveFamily B hZ)
    (h : X.HasResidueFieldGlobalFunctions) (s : X.base.left.1) :
    Function.Bijective (algebraMap (residueFieldValuedPoint B hZ X.base s).carrier
      (Space.globalFunctions B (Spec (.of (residueFieldValuedPoint B hZ X.base s).carrier))
        (residueFieldValuedPoint B hZ X.base s).contained
        (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom
          (residueFieldValuedPoint B hZ X.base s)))) :=
  (Space.bijective_algebraMap_fibreOverFieldValuedPoint_iff B integerBase hZ X.toBase.hom
    (residueFieldValuedPoint B hZ X.base s) X.total.2 (schemeSpace X.base).2).2 (h s)

/-- **From the residue fields to all fields.** If `κ(s) = H⁰(X_s, 𝒪_{X_s})` for every point `s` of
the base of a family of curves, then `k = H⁰(X_k, 𝒪_{X_k})` for every morphism `Spec k → S` from
the spectrum of a field. -/
theorem bijective_algebraMap_globalFunctions_fibre_of_residueField (X : CurveFamily B hZ)
    (h : X.HasResidueFieldGlobalFunctions)
    (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).1) :
    Function.Bijective (algebraMap p.carrier
      (Space.globalFunctions B (Spec (.of p.carrier)) p.contained
        (Space.fibreOverFieldValuedPoint B integerBase hZ X.toBase.hom p))) := by
  obtain ⟨K, hK, t, v⟩ := p
  change Function.Bijective (algebraMap K (Space.globalFunctions B (Spec (.of K)) hK
    (Space.restrictedFibre B integerBase hZ X.toBase.hom hK ⟨t⟩ v)))
  let φ : Spec (.of K) ⟶ X.base.left.1 := v.left.1
  let s : X.base.left.1 := φ (IsLocalRing.closedPoint K)
  let ι : X.base.left.1.residueField s ⟶ CommRingCat.of K :=
    X.base.left.1.descResidueField (Scheme.stalkClosedPointTo φ)
  let : Algebra (X.base.left.1.residueField s) K := ι.hom.toAlgebra
  let q := residueFieldValuedPoint B hZ X.base s
  let m : B.obj hK ⟶ B.obj q.contained := ⟨Spec.map ι⟩
  have hφ : Spec.map ι ≫ X.base.left.1.fromSpecResidueField s = φ :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K _ φ
  have hg : (⟨t⟩ : B.obj hK ⟶ B.obj hZ) = m ≫ (⟨q.toBase⟩ : B.obj q.contained ⟶ B.obj hZ) := by
    refine (Over.w v).symm.trans ?_
    apply ObjectProperty.hom_ext
    change φ ≫ X.base.hom.1 = Spec.map ι ≫ (X.base.left.1.fromSpecResidueField s ≫ X.base.hom.1)
    rw [← Category.assoc, hφ]
  have hv : (schemeSpace X.base).1.map (eqToHom (congrArg Over.mk hg.symm)).op v =
      (schemeSpace X.base).1.map (Over.homMk m rfl).op q.value := by
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    change (eqToHom (congrArg Over.mk hg.symm)).left.1 ≫ φ =
      Spec.map ι ≫ X.base.left.1.fromSpecResidueField s
    rw [hφ, Over.eqToHom_left, eqToHom_refl]
    rfl
  obtain ⟨e₁⟩ := Space.nonempty_restrictedFibre_iso_of_eq X.toBase.hom hK hg v
  obtain ⟨e₂⟩ := Space.nonempty_restrictedFibre_iso_relocalizeRestrict B integerBase hZ
    X.toBase.hom q.contained hK ⟨q.toBase⟩ m q.value
  have hfib := Space.isAlgebraicSpace_restrictedFibre B integerBase hZ X.toBase.hom X.total.2
    (schemeSpace X.base).2 q.contained ⟨q.toBase⟩ q.value
  refine (Space.bijective_algebraMap_globalFunctions_congr B
    (Space.isAlgebraicSpace_restrictedFibre B integerBase hZ X.toBase.hom X.total.2
      (schemeSpace X.base).2 hK ⟨t⟩ v)
    (isAlgebraicSpace_relocalizeRestrict B _ _ hK q.contained m _ hfib)
    (e₁ ≪≫ eqToIso (congrArg (Space.restrictedFibre B integerBase hZ X.toBase.hom hK _) hv) ≪≫
      e₂)).mpr ?_
  have hs := X.bijective_algebraMap_globalFunctions_residueFieldValuedPoint h s
  have hsep := (Space.isProper_restrictedFibre B integerBase hZ X.toBase.hom q.contained
    ⟨q.toBase⟩ q.value X.total.2 (schemeSpace X.base).2 X.proper).1
  have hfl := Space.isFlat_restrictedFibre B integerBase hZ X.toBase.hom q.contained ⟨q.toBase⟩
    q.value X.total.2 (schemeSpace X.base).2 X.flat
  have hfp := Space.isFinitePresentation_restrictedFibre B integerBase hZ X.toBase.hom q.contained
    ⟨q.toBase⟩ q.value X.total.2 (schemeSpace X.base).2 X.finitePresentation
  have hm : B.inclusion.map m = Spec.map (CommRingCat.ofHom
      (algebraMap (X.base.left.1.residueField s) K)) := rfl
  exact Space.bijective_algebraMap_globalFunctions_relocalizeRestrict_of_field B
    (k := X.base.left.1.residueField s) (hk := q.contained)
    (X := Space.restrictedFibre B integerBase hZ X.toBase.hom q.contained ⟨q.toBase⟩ q.value)
    hfib ((Space.isTerminal_yoneda_obj_base B _ q.contained).from _) hsep hfl hfp hs K hK m hm

/-- Let `f : X → S` be a family of curves with `κ(s) = H⁰(X_s, 𝒪_{X_s})` for every point `s ∈ S`.
Then `f_*𝒪_X = 𝒪_S` — the structure map `𝒪_S ⟶ f_*𝒪_X` is an isomorphism — and this holds
universally: the same is true of the base change of `f` along every morphism `Y ⟶ S` from an
algebraic space. -/
@[stacks 0E1J "(1)"]
theorem isIso_structureSharp_and_baseChange_of_residueField (X : CurveFamily B hZ)
    (h : X.HasResidueFieldGlobalFunctions) :
    IsIso (Space.structureSharp B integerBase hZ X.toBase) ∧
      ∀ (Y : AlgebraicSpaces B integerBase hZ) (g : Y ⟶ schemeSpace X.base),
        IsIso (Space.structureSharp B integerBase hZ (pullback.snd X.toBase g)) :=
  Space.isIso_structureSharp_and_baseChange_of_bijective_algebraMap_fibre B integerBase hZ
    X.toBase X.proper X.flat X.finitePresentation
    (X.bijective_algebraMap_globalFunctions_fibre_of_residueField h)

/-- Let `f : X → S` be a family of curves with `κ(s) = H⁰(X_s, 𝒪_{X_s})` for every point `s ∈ S`.
Then `R¹f_*𝒪_X` is a finite locally free `𝒪_S`-module: every object of the small étale site of
`S` has a covering on whose members it is finite free (Stacks 03DL (2)). -/
@[stacks 0E1J "(2)"]
theorem isFiniteLocallyFreeOnSite_firstDirectImage_of_residueField (X : CurveFamily B hZ)
    (h : X.HasResidueFieldGlobalFunctions) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (X.firstDirectImage B hZ) :=
  X.isFiniteLocallyFreeOnSite_firstDirectImage_of_bijective_algebraMap_fibre
    (X.bijective_algebraMap_globalFunctions_fibre_of_residueField h)

/-- Let `f : X → S` be a family of curves with `κ(s) = H⁰(X_s, 𝒪_{X_s})` for every point `s ∈ S`.
For every morphism `h : S' → S`, with `f' : X' → S'` the base change — that is, for every
morphism of families of curves `a : X' ⟶ X`, whose square is cartesian, over `h = a.baseMap` —
the base change map `h^*(R¹f_*𝒪_X) ⟶ R¹f'_*𝒪_{X'}`
(`AlgebraicGeometry.CurveFamily.firstDirectImageBaseChangeMap`) is an isomorphism. -/
@[stacks 0E1J "(3)"]
theorem isIso_firstDirectImageBaseChangeMap_of_residueField (X : CurveFamily B hZ)
    (h : X.HasResidueFieldGlobalFunctions) (F : CurveFamily B hZ) (a : F ⟶ X) :
    IsIso (firstDirectImageBaseChangeMap a) :=
  X.isIso_firstDirectImageBaseChangeMap_of_bijective_algebraMap_fibre
    (X.bijective_algebraMap_globalFunctions_fibre_of_residueField h) F a

/-- Let `f : X → S` be a family of curves with `κ(s) = H⁰(X_s, 𝒪_{X_s})` for every point `s ∈ S`.
For every morphism of families of curves `a : X' ⟶ X` over `h = a.baseMap`, there is an
isomorphism `h^*(R¹f_*𝒪_X) ≅ R¹f'_*𝒪_{X'}`: the base change map, which is invertible by
`AlgebraicGeometry.CurveFamily.isIso_firstDirectImageBaseChangeMap_of_residueField`
(Stacks 0E1J (3)). -/
theorem nonempty_modulePullback_firstDirectImage_iso_of_residueField (X : CurveFamily B hZ)
    (h : X.HasResidueFieldGlobalFunctions) (F : CurveFamily B hZ) (a : F ⟶ X) :
    Nonempty ((Space.modulePullback B integerBase hZ (schemeSpaceMap a.baseMap)).obj
        (X.firstDirectImage B hZ) ≅ F.firstDirectImage B hZ) :=
  have := X.isIso_firstDirectImageBaseChangeMap_of_residueField h F a
  ⟨asIso (firstDirectImageBaseChangeMap a)⟩

end CurveFamily

end AlgebraicGeometry

end
