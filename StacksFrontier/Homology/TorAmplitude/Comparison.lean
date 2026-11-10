module

public import StacksFrontier.Homology.TorAmplitude.Defs
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.Homology.TorAmplitude.Termwise
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Comparing a certified derived tensor product with the termwise tensor product

Let `R` be a commutative ring and let `derivedTensor` be any bifunctor on `D(R)` certified as a
derived tensor product in the sense of `StacksFrontier.Homology.TorAmplitude.Defs`, that is,
equipped with a `comparison` map to termwise tensoring together with the universal property
`isLeftDerived` making each `- ⊗ᴸ N[0]` the total left derived functor of `- ⊗ N`.  For a
bounded above complex `P` of flat modules the comparison map is invertible at `P`, so that the
derived tensor product of `P` really is computed by the termwise tensor complex.  Tor amplitude
of `Q P` is then equivalent to the termwise condition
`StacksDraft.TorAmplitude.Termwise.HasTorAmplitudeIn`.

Nothing here constructs a canonical derived tensor product, which is the content of Stacks 0BYI;
everything below is universally quantified over the certified derived tensor product instead.

## Main definitions

* `StacksDraft.TorAmplitude.termwiseDerived`: the total left derived functor of termwise
  tensoring by a module, together with its counit `termwiseDerivedCounit`.
* `StacksDraft.TorAmplitude.certifiedTensorHomologyIsoOfFlat`: the identification of the
  cohomology of the certified derived tensor product with the cohomology of the termwise tensor
  complex.

## Main results

* `StacksDraft.TorAmplitude.exists_projective_resolution`: a bounded above complex receives a
  quasi-isomorphism from a bounded above complex of projective modules, and
  `StacksDraft.TorAmplitude.kFlat_of_isStrictlyLE_projective`: such a complex is K-flat.
* `StacksDraft.TorAmplitude.quasiIso_tensorRight_map`,
  `StacksDraft.TorAmplitude.quasiIso_tensorLeft_map` and
  `StacksDraft.TorAmplitude.quasiIso_tensorModuleRight_map`: tensoring on either side with a
  K-flat complex, and tensoring termwise with a module, preserve quasi-isomorphisms.
* `StacksDraft.TorAmplitude.isIso_termwiseDerivedCounit_app`: the counit of `termwiseDerived` is
  invertible at a K-projective complex.
* `StacksDraft.TorAmplitude.isIso_comparison_app_of_isKProjective`: the comparison map is
  invertible at a K-projective complex.
* `StacksDraft.TorAmplitude.isIso_comparison_app_of_flat`: the comparison map is invertible at
  a bounded above complex of flat modules.
* `StacksDraft.TorAmplitude.hasTorAmplitude_iff_termwise_of_flat`: for such a complex,
  certified derived Tor amplitude is termwise Tor amplitude.

## Implementation notes

The proof is the direct one, through Mathlib's pointwise left derived functors, and avoids the
K-flat localizer.  Termwise tensoring by `N` satisfies the hypotheses of
Stacks 0794 (`hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex`), because a
bounded above acyclic complex of projective modules is K-projective and hence a zero object of
the homotopy category.  So its left derived functor along `Qh` is defined pointwise, and at a
K-projective complex the limit computing it is taken over a category with an initial object,
`Qh` being bijective on morphisms out of a K-projective complex.  Uniqueness of total left
derived functors transfers this to the given comparison map.  A bounded above complex is then
compared with a bounded above projective resolution of itself (Stacks 06XX), which requires
termwise tensoring to invert that quasi-isomorphism; this is where K-flatness enters, through a
bounded above projective resolution of the module `N` and the interchange square.

The K-flat input comes from the tagged providers: Stacks 064K is
`CochainComplex.KFlat.kFlat_of_flat` of `StacksFrontier.Homology.KFlat.Flat`, and Stacks 06Y0 is
`CochainComplex.KFlat.kFlat_tright_preserves_quasiIso` of
`StacksFrontier.Homology.KFlat.QuasiIso`.  Both are stated for a module universe independent of the
ring's, against `CochainComplex.KFlat`; at a coinciding universe that is the same
proposition as `CochainComplex.KFlat`, which since the collapse of the former onto it
transports them to the shared-universe form used here.  `quasiIso_tensorRight_map` below is the
cochain-level reading of 06Y0, obtained from its homotopy-category statement along
`HomotopyCategory.quotient_map_mem_quasiIso_iff`.  Turning it into its left-handed form needs
left and right tensoring by a complex to be identified, and the private, untagged
`tensorLeftIsoTensorRight` below stands in for the symmetric monoidal structure on cochain
complexes of Stacks 0FNI, which
is owned by another cluster.  It is a dedup target: it is assembled from Mathlib's
`HomologicalComplex.mapBifunctorFlipIso`, which already carries the Koszul sign, and the symmetry
of `ModuleCat R`, so once the 0FNI provider lands it should be deleted in favour of
`BraidedCategory.tensorLeftIsoTensorRight` for that braiding.

No `@[stacks]` attribute is attached to anything here: the tags this layer serves (0654, 066F,
066K, 066M, 066N, 066P, 0B66, 0B67, 0BYL, 0H75) are registered by their own providers, and
0BYI, 064K, 06Y0 and 0FNI belong to other clusters.

## References

* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
* [Stacks Project, Tag 0653](https://stacks.math.columbia.edu/tag/0653)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  CategoryTheory.MonoidalCategory HomologicalComplex

namespace StacksDraft.TorAmplitude

universe u w

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-! ### Projective resolutions of bounded above complexes -/

public instance hasExactColimitsOfShapeNat : HasExactColimitsOfShape ℕ (ModuleCat.{u} R) :=
  letI : AB5OfSize.{0, 0, u, u + 1} AddCommGrpCat.{u} :=
    AB5OfSize_of_univLE.{0, 0, u, u} AddCommGrpCat.{u}
  HasExactColimitsOfShape.domain_of_functor ℕ
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

/-- The projective modules, as a class of objects of `ModuleCat R`. -/
public abbrev projectiveObjects (R : Type u) [CommRing R] : ObjectProperty (ModuleCat.{u} R) :=
  fun X => Projective X

public instance : (projectiveObjects R).ContainsZero :=
  ⟨ModuleCat.of R (Fin 0 → R), ModuleCat.isZero_of_subsingleton _, inferInstance⟩

/-- The class of projective modules is closed under binary biproducts. -/
public lemma projectiveObjects_biprod (X Y : ModuleCat.{u} R)
    (hX : projectiveObjects R X) (hY : projectiveObjects R Y) :
    projectiveObjects R (X ⊞ Y) := by
  have := hX
  have := hY
  exact inferInstanceAs (Projective (X ⊞ Y))

/-- Every module is a quotient of a projective module. -/
public lemma projectiveObjects_cover (X : ModuleCat.{u} R) :
    ∃ (Y : ModuleCat.{u} R) (_ : projectiveObjects R Y) (p : Y ⟶ X), Epi p :=
  ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩

/-- Every bounded above cochain complex of modules receives a quasi-isomorphism from a bounded
above complex of projective modules: resolve the canonical truncations by Stacks 06XX, and use
that the inclusion of `τ_{≤ n} K` into `K` is an isomorphism once `K` is strictly bounded above
by `n`. -/
@[sga "4½ Etat_0 3.1.9" "Part 1, special case"]
public lemma exists_projective_resolution (K : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ)
    [K.IsStrictlyLE d] :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (π : P ⟶ K),
      P.IsStrictlyLE m ∧ (∀ i : ℤ, Projective (P.X i)) ∧ QuasiIso π := by
  obtain ⟨Q, f, -, hf, -, hLE, hQ, -, -⟩ := CochainComplex.exists_sequence_quasiIso_truncLE
    (projectiveObjects R) projectiveObjects_biprod projectiveObjects_cover K
  obtain ⟨n, hn⟩ : ∃ n : ℕ, d ≤ (n : ℤ) := ⟨d.toNat, Int.self_le_toNat d⟩
  have : K.IsStrictlyLE (n : ℤ) := K.isStrictlyLE_of_le d (n : ℤ) hn
  have hι : IsIso (K.ιTruncLE (n : ℤ)) := (K.isIso_ιTruncLE_iff (n : ℤ)).2 inferInstance
  exact ⟨Q n, (n : ℤ), f n ≫ K.ιTruncLE (n : ℤ), hLE n, fun i => hQ n i,
    quasiIso_comp (hφ := hf n) (hφ' := quasiIso_of_isIso _) _ _⟩

/-- A bounded above complex of projective modules is K-flat: projective modules are flat, so this
is Stacks 064K (`CochainComplex.KFlat.kFlat_of_flat`) read at a module universe equal to the
ring's, `CochainComplex.KFlat` being two-universe. -/
public lemma kFlat_of_isStrictlyLE_projective (K : CochainComplex (ModuleCat.{u} R) ℤ) (d : ℤ)
    [K.IsStrictlyLE d] (hproj : ∀ i : ℤ, Projective (K.X i)) : K.KFlat := by
  have hflat : ∀ i : ℤ, Module.Flat R (K.X i) := fun i => by
    have := hproj i
    infer_instance
  exact (CochainComplex.KFlat.kFlat_of_flat K d)

/-! ### Termwise tensoring versus tensoring with a module in degree zero -/

/-- The canonical map from the termwise tensor product `K ⊗ M` to the total tensor product of
`K` with `M` placed in cohomological degree `0`: in degree `n` it is the inclusion of the
`(n, 0)` summand of the antidiagonal. -/
@[expose]
public noncomputable def tensorSingleInclusion (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    (((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K ⟶
    (tensorRight ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)).obj K where
  f n := HomologicalComplex.ιTensorObj K
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) n 0 n (add_zero n)
  comm' n n' h := by
    obtain rfl : n + 1 = n' := h
    change HomologicalComplex.ιMapBifunctor K _ (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℤ) n 0 n (add_zero n) ≫
      (HomologicalComplex.mapBifunctor K _ (curriedTensor (ModuleCat.{u} R))
        (ComplexShape.up ℤ)).d n (n + 1) = _
    erw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (show n + 1 = n + 1 from rfl) 0 (n + 1) (add_zero _),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ n (show (0 : ℤ) + 1 = 1 from rfl) (n + 1) rfl]
    simp
    rfl

/-- All the other antidiagonal summands vanish, so `tensorSingleInclusion` is invertible. -/
public lemma tensorSingleInclusion_isIso (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso (tensorSingleInclusion M K) := by
  have hn : ∀ n, IsIso ((tensorSingleInclusion M K).f n) := by
    intro n
    let p : ((tensorRight
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)).obj K).X n ⟶
        K.X n ⊗ M :=
      HomologicalComplex.mapBifunctorDesc (K₁ := K)
        (K₂ := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)
        (F := curriedTensor (ModuleCat.{u} R)) (c := ComplexShape.up ℤ) (fun i j h =>
        if hj : j = 0 then eqToHom (by
          subst hj
          have hi : i = n := by simpa using h
          subst hi
          rfl)
        else 0)
    have hp : (tensorSingleInclusion M K).f n ≫ p = 𝟙 _ := by
      dsimp [tensorSingleInclusion, p, HomologicalComplex.ιTensorObj]
      rw [HomologicalComplex.ι_mapBifunctorDesc]
      simp
      rfl
    refine ⟨p, hp, ?_⟩
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    by_cases hj : j = 0
    · subst hj
      have hi : i = n := by simpa using h
      subst hi
      change (tensorSingleInclusion M K).f i ≫ p ≫ _ = _
      erw [← Category.assoc, hp, Category.id_comp]
    · exact (((tensoringLeft (ModuleCat.{u} R)).obj (K.X i)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M j hj)).eq_of_src _ _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- Termwise tensoring by `M` is naturally isomorphic to the total tensor product with `M`
placed in cohomological degree `0`. -/
public noncomputable def termwiseTensorSingleIso (M : ModuleCat.{u} R) :
    (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      tensorRight ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  refine NatIso.ofComponents (fun K =>
    letI := tensorSingleInclusion_isIso (R := R) M K
    asIso (tensorSingleInclusion M K)) ?_
  intro K K' g
  ext n : 1
  let S := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M
  change (g.f n ▷ M) ≫ HomologicalComplex.ιMapBifunctor K' S
      (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) n 0 n (add_zero n) =
    HomologicalComplex.ιMapBifunctor K S (curriedTensor (ModuleCat.{u} R))
      (ComplexShape.up ℤ) n 0 n (add_zero n) ≫
      (HomologicalComplex.mapBifunctorMap g (𝟙 S)
        (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ)).f n
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp
  rfl

/-! ### Identifying left and right tensoring by a complex

Mathlib has no braided structure on cochain complexes, and the Koszul braiding of Stacks 0FNI
belongs to another cluster.  All that is needed below is the induced natural isomorphism
`tensorLeft K ≅ tensorRight K`, which is Mathlib's flip isomorphism of totalized bifunctors
(`HomologicalComplex.mapBifunctorFlipIso`, whose statement carries the Koszul sign already)
transported along the symmetry of `ModuleCat R`.  The only missing ingredient is the action of a
natural isomorphism of bifunctors on the totalization, supplied by
`CochainComplex.DerivedTensor.mapBifunctorIso`.
-/

open CochainComplex.DerivedTensor in
/-- Left and right tensoring by a cochain complex agree, through the symmetry of `ModuleCat R`
and the flip isomorphism of totalized bifunctors. -/
private noncomputable def tensorLeftIsoTensorRight (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    tensorLeft K ≅ tensorRight K :=
  NatIso.ofComponents
    (fun L => mapBifunctorIso (BraidedCategory.curriedBraidingNatIso (ModuleCat.{u} R)) K L ≪≫
      mapBifunctorFlipIso L K (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ))
    (fun {L L'} f => by
      change mapBifunctorMap (𝟙 K) f (curriedTensor (ModuleCat.{u} R)) (ComplexShape.up ℤ) ≫
          (mapBifunctorIso (BraidedCategory.curriedBraidingNatIso (ModuleCat.{u} R)) K L').hom ≫
            (mapBifunctorFlipIso L' K (curriedTensor (ModuleCat.{u} R))
              (ComplexShape.up ℤ)).hom = _
      rw [reassoc_of% mapBifunctorIso_hom_naturality
          (BraidedCategory.curriedBraidingNatIso (ModuleCat.{u} R)) (𝟙 K) f,
        mapBifunctorFlipIso_hom_naturality]
      simp only [Iso.trans_hom, Category.assoc]
      rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring on the *right* with a K-flat complex preserves quasi-isomorphisms of cochain
complexes: if `f` is a quasi-isomorphism and `K` is K-flat, then `f ⊗ K` is a quasi-isomorphism.

This is Stacks 06Y0 (`CochainComplex.KFlat.kFlat_tright_preserves_quasiIso`), which is the
statement on the homotopy category, transported to cochain complexes along
`HomotopyCategory.quotient_map_mem_quasiIso_iff`, using that `tensorRight K` is the functor whose
descent to the homotopy category is `Tright K`. -/
public lemma quasiIso_tensorRight_map {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : K.KFlat)
    {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (f : X ⟶ Y) [QuasiIso f] :
    QuasiIso ((tensorRight K).map f) := by
  have hf : HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ _).map f) := by
    rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact inferInstanceAs (QuasiIso f)
  have h := CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K hK _ hf
  rw [MorphismProperty.inverseImage_iff] at h
  have h' : HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient _ _).map ((tensorRight K).map f)) := h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 h'

/-- Tensoring on the *left* with a K-flat complex preserves quasi-isomorphisms: the right-handed
statement `quasiIso_tensorRight_map` transported along `tensorLeftIsoTensorRight`. -/
public lemma quasiIso_tensorLeft_map (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : K.KFlat)
    {P S : CochainComplex (ModuleCat.{u} R) ℤ} (q : P ⟶ S) [QuasiIso q] :
    QuasiIso ((tensorLeft K).map q) := by
  have hqR : QuasiIso ((tensorRight K).map q) := quasiIso_tensorRight_map hK q
  exact (quasiIso_iff_of_arrow_mk_iso ((tensorLeft K).map q) ((tensorRight K).map q)
    (Arrow.isoMk ((tensorLeftIsoTensorRight K).app P) ((tensorLeftIsoTensorRight K).app S)
      ((tensorLeftIsoTensorRight K).hom.naturality q).symm)).2 hqR

/-- Termwise tensoring with a module inverts a quasi-isomorphism between K-flat complexes: use a
bounded above projective resolution `P_N ⟶ N[0]` of the module and the interchange square. -/
public lemma quasiIso_tensorModuleRight_map
    (N : ModuleCat.{u} R) {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (π : X ⟶ Y) [QuasiIso π]
    (hX : X.KFlat) (hY : Y.KFlat) :
    QuasiIso (((tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ)).map π) := by
  obtain ⟨PN, m, πN, hPNLE, hPNproj, hπN⟩ := exists_projective_resolution
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N) 0
  have := hπN
  have := hPNLE
  have hPN : PN.KFlat := kFlat_of_isStrictlyLE_projective PN m hPNproj
  have htop : QuasiIso ((tensorRight PN).map π) := quasiIso_tensorRight_map hPN π
  have hX' : QuasiIso ((tensorLeft X).map πN) := quasiIso_tensorLeft_map X hX πN
  have hY' : QuasiIso ((tensorLeft Y).map πN) := quasiIso_tensorLeft_map Y hY πN
  have hsq : (tensorLeft X).map πN ≫
      (tensorRight ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)).map π =
      (tensorRight PN).map π ≫ (tensorLeft Y).map πN := whisker_exchange π πN
  have hcomp : QuasiIso ((tensorLeft X).map πN ≫
      (tensorRight ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)).map π) := by
    rw [hsq]
    exact quasiIso_comp (hφ := htop) (hφ' := hY') _ _
  have hres : QuasiIso
      ((tensorRight ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj N)).map π) :=
    (quasiIso_iff_comp_left (hφ := hX') _ _).1 hcomp
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk ((termwiseTensorSingleIso N).app X) ((termwiseTensorSingleIso N).app Y)
      (((termwiseTensorSingleIso N).hom.naturality π).symm))).2 hres

/-! ### The left derived functor of termwise tensoring exists pointwise -/

/-- Termwise tensoring by `N` turns a bounded above acyclic complex of projective modules into
an acyclic complex: such a complex is K-projective, hence a zero object of the homotopy
category, and an additive functor preserves zero objects. -/
lemma acyclic_tensorModuleRight_of_projective (N : ModuleCat.{u} R) (a : ℤ)
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hLE : L.IsStrictlyLE a)
    (hproj : ∀ n : ℤ, Projective (L.X n)) (hac : L.Acyclic) :
    (((tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic := by
  have := hLE
  have := hproj
  have : L.IsKProjective := CochainComplex.isKProjective_of_projective L a
  have hz : IsZero ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj L) := by
    rw [IsZero.iff_id_eq_zero]
    exact CochainComplex.IsKProjective.leftOrthogonal L (𝟙 _)
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic L).2 hac)
  have hz2 := ((tensorModuleRight N).mapHomotopyCategory (ComplexShape.up ℤ)).map_isZero hz
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic]
  exact (HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} R)).prop_of_isZero hz2

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- Termwise tensoring by `N`, read on the homotopy category and followed by the localization
to the derived category. -/
public noncomputable abbrev termwiseTensorHomotopy (N : ModuleCat.{u} R) :
    HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (tensorModuleRight N).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- Stacks 0794 applies to termwise tensoring by `N`: its left derived functor along
`Qh : K(R) ⥤ D(R)` is defined at every object. -/
instance hasPointwiseLeftDerivedFunctor_termwiseTensor (N : ModuleCat.{u} R) :
    (termwiseTensorHomotopy N).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  have hpf : PreservesFiniteColimits (tensorModuleRight (R := R) N) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  have hpc : PreservesColimitsOfShape ℕ (tensorModuleRight (R := R) N) :=
    preservesColimitsOfShape_of_natIso (BraidedCategory.tensorLeftIsoTensorRight N)
  exact CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex
    _ (projectiveObjects R) projectiveObjects_biprod projectiveObjects_cover
    (fun a L hLE hP hac => acyclic_tensorModuleRight_of_projective N a L hLE hP hac)

/-! ### Kan extension transport between the homotopy category and complexes -/

/-- Precomposition which is fully faithful on functor categories preserves the right Kan
universal property. -/
public lemma isRightKanExtension_precomp_of_fullyFaithful
    {C C' D H : Type*} [Category* C] [Category* C'] [Category* D] [Category* H]
    (E : C' ⥤ C) [((whiskeringLeft C' C H).obj E).Full]
    [((whiskeringLeft C' C H).obj E).Faithful]
    (L : C ⥤ D) (F : C ⥤ H) (G : D ⥤ H) (α : L ⋙ G ⟶ F)
    [G.IsRightKanExtension α] :
    G.IsRightKanExtension ((Functor.associator E L G).hom ≫ whiskerLeft E α) := by
  have : (RightExtension.precomp L F E).IsEquivalence := by
    dsimp only [RightExtension.precomp]
    infer_instance
  let h := (IsTerminal.isTerminalIffObj (RightExtension.precomp L F E)
    (RightExtension.mk G α)).1 (G.isUniversalOfIsRightKanExtension α)
  exact ⟨⟨IsTerminal.ofIso h (CostructuredArrow.isoMk (Iso.refl G))⟩⟩

/-- A total left derived functor along `Qh` is a total left derived functor along `Q`:
precomposition with the homotopy quotient is fully faithful on functor categories, so the two
right Kan universal properties agree. -/
public lemma isLeftDerivedFunctor_of_homotopyCategory {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] {H : Type*} [Category* H]
    (U : CochainComplex C ℤ ⥤ H) (Uh : HomotopyCategory C (ComplexShape.up ℤ) ⥤ H)
    (e : HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ Uh ≅ U)
    (F : DerivedCategory C ⥤ H) (α : DerivedCategory.Qh ⋙ F ⟶ Uh)
    (β : DerivedCategory.Q ⋙ F ⟶ U)
    (hβ : whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ)) α =
      whiskerRight (DerivedCategory.quotientCompQhIso C).hom F ≫ β ≫ e.inv)
    [F.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))] :
    F.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) := by
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension F α
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  have hk := isRightKanExtension_precomp_of_fullyFaithful
    (HomotopyCategory.quotient C (ComplexShape.up ℤ)) DerivedCategory.Qh Uh F α
  have hke : F.IsRightKanExtension
      (whiskerRight (DerivedCategory.quotientCompQhIso C).hom F ≫ β) := by
    apply (Functor.isRightKanExtension_iff_of_iso₂
      ((Functor.associator (HomotopyCategory.quotient C (ComplexShape.up ℤ))
        DerivedCategory.Qh F).hom ≫
        whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ)) α)
      (whiskerRight (DerivedCategory.quotientCompQhIso C).hom F ≫ β) e (Iso.refl F) ?_).mp hk
    rw [hβ]
    ext X
    simp
  rw [Functor.isLeftDerivedFunctor_iff_isRightKanExtension]
  apply (Functor.isRightKanExtension_iff_postcomp₁ (𝟭 _)
    (((HomotopyCategory.quotient C (ComplexShape.up ℤ)) ⋙ DerivedCategory.Qh).rightUnitor ≪≫
      DerivedCategory.quotientCompQhIso C) β).2
  have := hke
  apply Functor.isRightKanExtension_of_iso F.leftUnitor.symm
    (whiskerRight (DerivedCategory.quotientCompQhIso C).hom F ≫ β)
  ext X
  simp

/-- A K-projective complex is an initial object of the category of objects of the homotopy
category under its own image in the derived category, because `Qh` is bijective on morphisms out
of a K-projective complex. -/
public noncomputable def isInitialStructuredArrowMkId {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (P : CochainComplex C ℤ) [P.IsKProjective] :
    IsInitial (StructuredArrow.mk
      (𝟙 (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)))) :=
  let e : ∀ X : HomotopyCategory C (ComplexShape.up ℤ),
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P ⟶ X) ≃
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P) ⟶
          DerivedCategory.Qh.obj X) :=
    fun X => Equiv.ofBijective _ (CochainComplex.IsKProjective.Qh_map_bijective P X)
  IsInitial.ofUniqueHom
    (fun g => StructuredArrow.homMk ((e g.right).symm g.hom) (by
      have : DerivedCategory.Qh.map ((e g.right).symm g.hom) = g.hom :=
        (e g.right).apply_symm_apply g.hom
      simpa using this))
    (fun g m => by
      apply StructuredArrow.hom_ext
      refine (e g.right).injective ?_
      have hw : DerivedCategory.Qh.map m.right = g.hom := by
        simpa using StructuredArrow.w m
      exact hw.trans ((e g.right).apply_symm_apply g.hom).symm)

/-! ### A certified total left derived functor of termwise tensoring -/

/-- The total left derived functor of termwise tensoring by `N`, on the derived category. -/
public noncomputable def termwiseDerived (N : ModuleCat.{u} R) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R) :=
  (termwiseTensorHomotopy N).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))

/-- Its counit, on the homotopy category. -/
noncomputable def termwiseDerivedCounitHomotopy (N : ModuleCat.{u} R) :
    DerivedCategory.Qh ⋙ termwiseDerived N ⟶ termwiseTensorHomotopy N :=
  (termwiseTensorHomotopy N).totalLeftDerivedCounit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))

instance isLeftDerivedFunctor_termwiseDerivedCounitHomotopy (N : ModuleCat.{u} R) :
    (termwiseDerived N).IsLeftDerivedFunctor (termwiseDerivedCounitHomotopy N)
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := by
  dsimp only [termwiseDerived, termwiseDerivedCounitHomotopy]
  infer_instance

/-- Termwise tensoring read on the homotopy category, precomposed with the homotopy quotient,
is termwise tensoring on complexes followed by the localization. -/
public noncomputable def quotientCompTermwiseTensorIso (N : ModuleCat.{u} R) :
    HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ) ⋙
        termwiseTensorHomotopy N ≅
      (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight
      ((tensorModuleRight N).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft
      ((tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R))

/-- The counit of `termwiseDerived N`, on complexes. -/
public noncomputable def termwiseDerivedCounit (N : ModuleCat.{u} R) :
    DerivedCategory.Q ⋙ termwiseDerived N ⟶
      (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  whiskerRight (DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)).inv (termwiseDerived N) ≫
    whiskerLeft (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (termwiseDerivedCounitHomotopy N) ≫ (quotientCompTermwiseTensorIso N).hom

/-- `termwiseDerived N` is the total left derived functor of termwise tensoring by `N` along the
localization `DerivedCategory.Q` from complexes, with counit `termwiseDerivedCounit N`. -/
public instance isLeftDerivedFunctor_termwiseDerivedCounit (N : ModuleCat.{u} R) :
    (termwiseDerived N).IsLeftDerivedFunctor (termwiseDerivedCounit N)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) :=
  isLeftDerivedFunctor_of_homotopyCategory _ (termwiseTensorHomotopy N)
    (quotientCompTermwiseTensorIso N) (termwiseDerived N) (termwiseDerivedCounitHomotopy N)
    (termwiseDerivedCounit N) (by
      ext X
      dsimp only [termwiseDerivedCounit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app]
      rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      simp)

/-- The counit of the total left derived functor of termwise tensoring is invertible at a
K-projective complex: the pointwise limit computing it is taken over a category with an initial
object. -/
lemma isIso_termwiseDerivedCounitHomotopy_app (N : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective] :
    IsIso ((termwiseDerivedCounitHomotopy N).app
      ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj P)) := by
  have hpt := hasPointwiseLeftDerivedFunctor_termwiseTensor (R := R) N
  have hptw : (RightExtension.mk (termwiseDerived N)
      (termwiseDerivedCounitHomotopy N)).IsPointwiseRightKanExtension :=
    Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
      (termwiseDerived N) (termwiseDerivedCounitHomotopy N)
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
  have hat := hptw (DerivedCategory.Qh.obj
    ((HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj P))
  have h := hat.isIso_π_app_of_isInitial _ (isInitialStructuredArrowMkId P)
  simpa using h

/-- The counit of the total left derived functor of termwise tensoring by `N` is invertible at a
K-projective complex.  This is `isIso_termwiseDerivedCounitHomotopy_app` read on complexes; note
that a bounded above complex of projective modules is K-projective, so together with
`exists_projective_resolution` this computes `termwiseDerived N` on bounded above complexes. -/
public lemma isIso_termwiseDerivedCounit_app (N : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective] :
    IsIso ((termwiseDerivedCounit N).app P) := by
  have := isIso_termwiseDerivedCounitHomotopy_app N P
  dsimp only [termwiseDerivedCounit, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  infer_instance


/-! ### The comparison theorem -/

variable {derivedTensor : DerivedCategory (ModuleCat.{u} R) ⥤
  DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R)}

/-- For a K-projective complex, the comparison map of an arbitrary certified derived tensor
product is invertible. -/
public theorem isIso_comparison_app_of_isKProjective
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
          (comparison N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (P : CochainComplex (ModuleCat.{u} R) ℤ) [P.IsKProjective] (N : ModuleCat.{u} R) :
    IsIso ((comparison N).app P) := by
  have := isLeftDerived N
  have hβ : IsIso ((termwiseDerivedCounit N).app P) := isIso_termwiseDerivedCounit_app N P
  set τ := Functor.leftDerivedNatTrans (termwiseDerived N)
    (derivedTensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N))
    (termwiseDerivedCounit N) (comparison N)
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) (𝟙 _) with hτ
  have hiso : IsIso (τ.app (DerivedCategory.Q.obj P)) := by
    have h : IsIso ((Functor.leftDerivedNatIso (termwiseDerived N)
        (derivedTensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N))
        (termwiseDerivedCounit N) (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
        (Iso.refl _)).hom.app (DerivedCategory.Q.obj P)) := inferInstance
    simpa using h
  have hkey : IsIso (τ.app (DerivedCategory.Q.obj P) ≫ (comparison N).app P) := by
    rw [hτ, Functor.leftDerivedNatTrans_app]
    simpa using hβ
  exact IsIso.of_isIso_comp_left (τ.app (DerivedCategory.Q.obj P)) ((comparison N).app P)

/-- **The comparison theorem.** For a bounded above complex `P` of flat modules, an arbitrary
certified derived tensor product agrees with the termwise tensor product through its own
comparison map. -/
public theorem isIso_comparison_app_of_flat
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
          (comparison N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbounded : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hflat : ∀ i : ℤ, Module.Flat R (P.X i)) (N : ModuleCat.{u} R) :
    IsIso ((comparison N).app P) := by
  obtain ⟨d, hd⟩ := hbounded
  have hPLE : P.IsStrictlyLE d := (CochainComplex.isStrictlyLE_iff P d).2 hd
  have hPKF : P.KFlat :=
    (CochainComplex.KFlat.kFlat_of_flat P d)
  obtain ⟨P', m, π, hP'LE, hP'proj, hπ⟩ := exists_projective_resolution P d
  have := hP'LE
  have := hπ
  have : P'.IsKProjective := CochainComplex.isKProjective_of_projective P' m
  have h1 : IsIso ((comparison N).app P') :=
    isIso_comparison_app_of_isKProjective comparison isLeftDerived P' N
  have h2 : QuasiIso (((tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ)).map π) :=
    quasiIso_tensorModuleRight_map N π (kFlat_of_isStrictlyLE_projective P' m hP'proj) hPKF
  have h3 : IsIso (DerivedCategory.Q.map
      (((tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ)).map π)) := by
    have := h2
    infer_instance
  have hkey : IsIso ((DerivedCategory.Q ⋙ derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).map π ≫
      (comparison N).app P) := by
    rw [(comparison N).naturality π]
    dsimp only [Functor.comp_map]
    infer_instance
  have h4 : IsIso ((DerivedCategory.Q ⋙ derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).map π) := by
    dsimp only [Functor.comp_map]
    infer_instance
  exact (isIso_comp_left_iff _ _).1 hkey

/-! ### Consequences -/

/-- For a bounded above complex of flat modules, the cohomology of an arbitrary certified
derived tensor product is the cohomology of the termwise tensor complex, through the certified
comparison map. -/
public noncomputable def certifiedTensorHomologyIsoOfFlat
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
          (comparison N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbounded : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hflat : ∀ i : ℤ, Module.Flat R (P.X i)) (N : ModuleCat.{u} R) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((derivedTensor.obj (DerivedCategory.Q.obj P)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)) ≅
      (((tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj P).homology i :=
  haveI := isIso_comparison_app_of_flat comparison isLeftDerived P hbounded hflat N
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
      (asIso ((comparison N).app P)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app _

/-- For a bounded above complex of flat modules, certified derived Tor amplitude is equivalent
to the vanishing of the cohomology of the termwise tensor complexes, that is, to
`StacksDraft.TorAmplitude.Termwise.HasTorAmplitudeIn`. -/
public theorem hasTorAmplitude_iff_termwise_of_flat
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
          (comparison N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hbounded : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hflat : ∀ i : ℤ, Module.Flat R (P.X i)) (a b : ℤ) :
    HasTorAmplitude derivedTensor comparison isLeftDerived (DerivedCategory.Q.obj P) a b ↔
      ∀ (M : ModuleCat.{u} R) (i : ℤ), (i < a ∨ b < i) →
        IsZero ((StacksDraft.TorAmplitude.Termwise.tensorComplex P M).homology i) :=
  have hmem : ∀ i : ℤ, i ∉ Set.Icc a b ↔ (i < a ∨ b < i) := fun i => by
    simp only [Set.mem_Icc, not_and_or, not_le]
  ⟨fun h M i hi => (h M i ((hmem i).2 hi)).of_iso
      (certifiedTensorHomologyIsoOfFlat comparison isLeftDerived P hbounded hflat M i).symm,
    fun h M i hi => (h M i ((hmem i).1 hi)).of_iso
      (certifiedTensorHomologyIsoOfFlat comparison isLeftDerived P hbounded hflat M i)⟩

end StacksDraft.TorAmplitude
