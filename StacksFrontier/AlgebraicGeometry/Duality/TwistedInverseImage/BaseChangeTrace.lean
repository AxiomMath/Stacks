module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChange
public import StacksFrontier.CategoryTheory.Monoidal.ComparisonMapBaseChange

/-!
# Trace maps, units and the comparison map under Tor independent base change

For a cartesian square of quasi-compact and quasi-separated schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` and `g` Tor independent, the base change map `β : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*` of
derived direct image and the base change map `α : L(g')^* ∘ a ⟶ a' ∘ Lg^*` of the twisted inverse
images ([Stacks, Tag 0AA6]) are compatible with the counits (trace maps) and the units of
`Rf_* ⊣ a` and `Rf'_* ⊣ a'`.

## Main results

* `Stacks.Duality.map_trace_eq_baseChange_comp_trace_of_torIndependent` — [Stacks, Tag 0B6J].
* `Stacks.Duality.map_unit_comp_baseChange_comp_baseChange_of_torIndependent` —
  [Stacks, Tag 0B6K].
* `Stacks.Duality.twistedInverseImageCompareWithPullback_eq_comparisonMap` — the map of
  Equation 48.8.0.1 through the comparison map of the monoidal adjunction `Lf^* ⊣ Rf_*`.
* `Stacks.Duality.map_twistedInverseImageCompareWithPullback_comp_baseChange_of_torIndependent` —
  [Stacks, Tag 0B6P].
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Duality

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- `ξ` of a Tor independent cartesian square, in the shape of
`Stacks.CategoryTheory.BaseChange.rightAdjointSquare`, is invertible ([Stacks, Tag 0A9K]). -/
theorem isIso_rightAdjointSquare_of_torIndependent (sq : IsPullback g' f' f g)
    (hTor : TorIndependent f g) :
    IsIso (Stacks.CategoryTheory.BaseChange.rightAdjointSquare
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
        (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
        (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g'))
        (quasiCoherentDerivedPullbackCompIso f' g)
        (quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w)
        (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))) := by
  rw [← twistedInverseImagePushforwardBaseChange_eq_rightAdjointSquare]
  exact isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor

/-- **[Stacks, Tag 0B6J] (trace map and base change).** For a cartesian square of
quasi-compact and quasi-separated schemes with `f` and `g` Tor independent, the maps
`1 ⋆ Tr_f : Lg^* ∘ Rf_* ∘ a ⟶ Lg^*` and `Tr_{f'} ⋆ 1 : Rf'_* ∘ a' ∘ Lg^* ⟶ Lg^*` agree via the
base change maps `β : Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*` and `α : L(g')^* ∘ a ⟶ a' ∘ Lg^*`
(Equation 48.5.0.1): `Lg^*(Tr_{f,K}) = Tr_{f',Lg^*K} ∘ Rf'_*(α_K) ∘ β_{a(K)}` for every `K`. -/
@[stacks 0B6J]
theorem map_trace_eq_baseChange_comp_trace_of_torIndependent (sq : IsPullback g' f' f g)
    (hTor : TorIndependent f g) (K : quasiCoherentDerivedCategory Y) :
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
    (quasiCoherentDerivedPullback g (isQuasicoherent_homology_derivedPullback' g)).map
        ((twistedInverseImageAdjunction f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).counit.app K) =
      (quasiCoherentDerivedBaseChange g' f' f g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
          (isQuasicoherent_homology_derivedPullback' g)
          (isQuasicoherent_homology_derivedPullback' g') sq.w).app
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K) ≫
        (quasiCoherentDerivedPushforward f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).map
          ((twistedInverseImageBaseChangeMap g' f' f g
            (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
            (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq).app K) ≫
          (twistedInverseImageAdjunction f'
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).counit.app
            ((quasiCoherentDerivedPullback g
              (isQuasicoherent_homology_derivedPullback' g)).obj K) := by
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
  have := isIso_rightAdjointSquare_of_torIndependent sq hTor
  rw [quasiCoherentDerivedBaseChange_eq_twoSquare,
    twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange sq]
  exact Stacks.CategoryTheory.BaseChange.map_counit_eq_twoSquare_comp_map_rightAdjointBaseChange
    _ _ _ _ _ _ _ _ K

/-- **[Stacks, Tag 0B6K] (unit and base change).** For a cartesian square of quasi-compact and
quasi-separated schemes with `f` and `g` Tor independent, the maps
`1 ⋆ η_f : L(g')^* ⟶ L(g')^* ∘ a ∘ Rf_*` and `η_{f'} ⋆ 1 : L(g')^* ⟶ a' ∘ Rf'_* ∘ L(g')^*` agree
via the base change maps `α` (Equation 48.5.0.1) and `β`:
`a'(β_M) ∘ α_{Rf_*M} ∘ L(g')^*(η_{f,M}) = η_{f',L(g')^*M}` for every `M`. -/
@[stacks 0B6K]
theorem map_unit_comp_baseChange_comp_baseChange_of_torIndependent (sq : IsPullback g' f' f g)
    (hTor : TorIndependent f g) (M : quasiCoherentDerivedCategory X) :
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
    (quasiCoherentDerivedPullback g' (isQuasicoherent_homology_derivedPullback' g')).map
        ((twistedInverseImageAdjunction f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).unit.app M) ≫
      (twistedInverseImageBaseChangeMap g' f' f g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq).app
          ((quasiCoherentDerivedPushforward f
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj M) ≫
        (twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).map
          ((quasiCoherentDerivedBaseChange g' f' f g
            (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
            (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
            (isQuasicoherent_homology_derivedPullback' g)
            (isQuasicoherent_homology_derivedPullback' g') sq.w).app M) =
      (twistedInverseImageAdjunction f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).unit.app
        ((quasiCoherentDerivedPullback g'
          (isQuasicoherent_homology_derivedPullback' g')).obj M) := by
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
  have := isIso_rightAdjointSquare_of_torIndependent sq hTor
  rw [quasiCoherentDerivedBaseChange_eq_twoSquare,
    twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange sq]
  exact Stacks.CategoryTheory.BaseChange.map_unit_comp_rightAdjointBaseChange_comp_map_twoSquare
    _ _ _ _ _ _ _ _ M

/-- Conjugating `p ▷ B ≫ A' ◁ x` by an identification of a bifunctor with the tensor product. -/
@[reassoc]
lemma tensorIso_inv_comp_map_comp_hom {C : Type*} [Category C] [MonoidalCategory C]
    (T : C ⥤ C ⥤ C) (ι : T ≅ curriedTensor C) {A A' B B' : C} (p : A ⟶ A') (x : B ⟶ B') :
    (ι.inv.app A).app B ≫ (T.map p).app B ≫ (T.obj A').map x ≫ (ι.hom.app A').app B' =
      (p ⊗ₘ x) := by
  have h₁ : (T.map p).app B ≫ (ι.hom.app A').app B = (ι.hom.app A).app B ≫ p ▷ B :=
    congrArg (fun t => t.app B) (ι.hom.naturality p)
  have h₂ : (T.obj A').map x ≫ (ι.hom.app A').app B' = (ι.hom.app A').app B ≫ A' ◁ x :=
    (ι.hom.app A').naturality x
  rw [h₂, reassoc_of% h₁, ← NatTrans.comp_app_assoc, ← NatTrans.comp_app, Iso.inv_hom_id,
    NatTrans.id_app, NatTrans.id_app, Category.id_comp, MonoidalCategory.tensorHom_def]

/-- **Equation 48.8.0.1 through the comparison map of the monoidal adjunction**: the map
`Lf^*K ⊗ᴸ a(𝒪_Y) ⟶ a(K)` of [Stacks, Tag 0A9S] is the comparison map of `Lf^* ⊣ Rf_*` at
`(K, 𝒪_Y)`, read through the identification of `⊗ᴸ` with the tensor product of `D_QCoh`, followed
by `a` of the right unitor. -/
theorem twistedInverseImageCompareWithPullback_eq_comparisonMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (K : quasiCoherentDerivedCategory Y) :
    twistedInverseImageCompareWithPullback f
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (quasiCoherentDerivedPullbackTensorIso f).hom (quasiCoherentDerivedTensorRightUnitor Y) K =
      ((quasiCoherentDerivedTensorIsoCurriedTensor X).hom.app
          ((quasiCoherentDerivedPullback' f).obj K)).app
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (DerivedPushforward.derivedStructureSheaf Y)) ≫
        (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).comparisonMap
          (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
          K (DerivedPushforward.derivedStructureSheaf Y) ≫
        (twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).map
          (K ◁ eqToHom (tensorUnit_quasiCoherentDerivedCategory Y).symm ≫ (ρ_ K).hom) := by
  have e := compareWithPullbackTensor_eq_comparisonMap f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (quasiCoherentDerivedPullbackTensorIso f).hom (quasiCoherentDerivedPullbackTensorIso_hom_app f)
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    K (DerivedPushforward.derivedStructureSheaf Y)
  simp only [twistedInverseImageCompareWithPullback, compareWithPullback, e, Category.assoc,
    quasiCoherentDerivedTensorRightUnitor_hom_app, ← Functor.map_comp, ← NatTrans.comp_app_assoc,
    ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app, Category.id_comp]

/-- **[Stacks, Tag 0B6P] (Lemma 48.8.2).** For a cartesian square of quasi-compact and
quasi-separated schemes with `f` and `g` Tor independent and `K ∈ D_QCoh(𝒪_Y)`, the square

```
L(g')^*(Lf^*K ⊗ᴸ a(𝒪_Y)) ──────────────→ L(g')^*a(K)
          │                                    │ α_K
          ↓                                    ↓
L(f')^*Lg^*K ⊗ᴸ a'(𝒪_{Y'}) ─────────────→ a'(Lg^*K)
```

commutes, where the horizontal arrows are the maps of Equation 48.8.0.1 for `K` and `Lg^*K`, `α`
is the base change map of Equation 48.5.0.1, and the left vertical arrow is the tensor comparison
of `L(g')^*`, the identification `L(g')^*Lf^* ≅ L(f')^*Lg^*` of the composites around the
square, and `α` at `𝒪_Y` followed by `a'` of `Lg^*𝒪_Y ≅ 𝒪_{Y'}`. -/
@[stacks 0B6P]
theorem map_twistedInverseImageCompareWithPullback_comp_baseChange_of_torIndependent
    (sq : IsPullback g' f' f g) (hTor : TorIndependent f g) (K : quasiCoherentDerivedCategory Y) :
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
    (quasiCoherentDerivedPullback' g').map
        (twistedInverseImageCompareWithPullback f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (quasiCoherentDerivedPullbackTensorIso f).hom (quasiCoherentDerivedTensorRightUnitor Y)
          K) ≫
      (twistedInverseImageBaseChangeMap g' f' f g
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq).app K =
      (quasiCoherentDerivedPullbackTensorIso g').hom.app
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
            (DerivedPushforward.derivedStructureSheaf Y), (quasiCoherentDerivedPullback' f).obj K) ≫
        ((quasiCoherentDerivedTensor X').map
          (((quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w) ≪≫
            (quasiCoherentDerivedPullbackCompIso f' g).symm).hom.app K)).app
          ((quasiCoherentDerivedPullback' g').obj
            ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
              (DerivedPushforward.derivedStructureSheaf Y))) ≫
        ((quasiCoherentDerivedTensor X').obj
            ((quasiCoherentDerivedPullback' f').obj ((quasiCoherentDerivedPullback' g).obj K))).map
          ((twistedInverseImageBaseChangeMap g' f' f g
              (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
              (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
              (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
              (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq).app
              (DerivedPushforward.derivedStructureSheaf Y) ≫
            (twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).map
              ((quasiCoherentDerivedPullback' g).map
                  (eqToHom (tensorUnit_quasiCoherentDerivedCategory Y).symm) ≫
                Functor.OplaxMonoidal.η (quasiCoherentDerivedPullback' g) ≫
                eqToHom (tensorUnit_quasiCoherentDerivedCategory Y'))) ≫
        twistedInverseImageCompareWithPullback f'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
          (quasiCoherentDerivedPullbackTensorIso f').hom (quasiCoherentDerivedTensorRightUnitor Y')
          ((quasiCoherentDerivedPullback' g).obj K) := by
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sq hTor
  have := isIso_rightAdjointSquare_of_torIndependent sq hTor
  let hpg' := isQuasicoherent_homology_derivedPushforward_of_qcqs g'
  let hpf := isQuasicoherent_homology_derivedPushforward_of_qcqs f
  let hpf' := isQuasicoherent_homology_derivedPushforward_of_qcqs f'
  let hpg := isQuasicoherent_homology_derivedPushforward_of_qcqs g
  let adjf := quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpf
  let adjf' := quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f') hpf'
  let adjg := quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g) hpg
  let adjg' := quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g') hpg'
  let eg := quasiCoherentDerivedPullbackCompIso f' g
  let ef := quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w
  let adja := twistedInverseImageAdjunction f hpf
  let adja' := twistedInverseImageAdjunction f' hpf'
  have : NatTrans.IsMonoidal ef.hom :=
    inferInstanceAs (NatTrans.IsMonoidal ((quasiCoherentDerivedPullbackCompIso g' f).hom ≫
      (quasiCoherentDerivedPullbackCongr sq.w).hom))
  have : IsIso (Stacks.CategoryTheory.BaseChange.twoSquare adjf adjf' eg ef) := by
    have h := isIso_quasiCoherentDerivedBaseChange_natTrans hpg' hpf hpf' hpg sq hTor
    rwa [quasiCoherentDerivedBaseChange_eq_twoSquare] at h
  have hsq := Stacks.CategoryTheory.BaseChange.squareComposite_δ_compat eg ef
    (NatTrans.IsMonoidal.δ_comp_tensorHom eg.hom) (NatTrans.IsMonoidal.δ_comp_tensorHom ef.hom)
  have key := Stacks.CategoryTheory.BaseChange.comparisonMap_unit_baseChange adjf adjf' adjg adjg'
    eg ef hsq adja adja' (tensorUnit_quasiCoherentDerivedCategory Y)
    (tensorUnit_quasiCoherentDerivedCategory Y') K
  have hp : ((quasiCoherentDerivedPullbackCompIso g' f ≪≫ quasiCoherentDerivedPullbackCongr sq.w) ≪≫
      (quasiCoherentDerivedPullbackCompIso f' g).symm).hom.app K =
      (Stacks.AffineProjectionFormula.squareCompositeIso eg ef).inv.app K := rfl
  rw [twistedInverseImageCompareWithPullback_eq_comparisonMap f,
    twistedInverseImageCompareWithPullback_eq_comparisonMap f',
    quasiCoherentDerivedPullbackTensorIso_hom_app, hp,
    twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange sq, Functor.map_comp,
    Category.assoc, key]
  simp only [Category.assoc]
  dsimp only [Functor.comp_obj]
  rw [tensorIso_inv_comp_map_comp_hom_assoc]

end Stacks.Duality

end
