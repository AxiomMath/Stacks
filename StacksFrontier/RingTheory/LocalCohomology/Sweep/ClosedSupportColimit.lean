module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.RingTheory.LocalCohomology.ModulesSupportedIn
public import StacksFrontier.RingTheory.LocalCohomology.TorsionColimit
public import StacksCore.Tactic.StacksAttribute

/-!
# Local cohomology with arbitrary support as a colimit over closed supports

Let `A` be a commutative ring and `T ⊆ Spec(A)` a subset. Degree-zero sections with support in
`T` are by construction the filtered union of the sections supported in a closed subset
`V(I) ⊆ T`, and this file promotes that union to the derived level: for every object `K` of
`D(A)` the canonical comparison
$$ \operatorname*{colim}_{V(I) \subseteq T} H^i_{V(I)}(K) \longrightarrow H^i_T(K) $$
is an isomorphism, naturally in `K`. This is Tag 0EF1.

The closed subsets of `T` are indexed by the ideals `I` with `V(I) ⊆ T`, ordered by reverse
inclusion, which is a filtered category. Each stage is the total right derived functor of
sections with support in `V(I)`, and the transition maps and the maps to the `T`-stage are
obtained by deriving the literal inclusions of section submodules; their compatibility with the
canonical derived units is what fixes the normalization.

## Main definitions

* `Stacks.LocalCohomology.ClosedSupportIdeal` — the filtered index category of closed subsets
  of `T`.
* `Stacks.LocalCohomology.sectionsWithSupportInInclusion` and
  `Stacks.LocalCohomology.derivedSectionsWithSupportInInclusion` — the inclusion of supported
  sections and its total right derived functor.
* `Stacks.LocalCohomology.closedSupportDiagram` — the diagram of closed-support local
  cohomology, functorial in the derived object.
* `Stacks.LocalCohomology.closedSupportStageComparison` and
  `Stacks.LocalCohomology.closedSupportCocone` — the canonical maps to local cohomology with
  support in `T`.
* `Stacks.LocalCohomology.colimitClosedSupportComparison` — the comparison induced by that
  cocone.

## Main results

* `Stacks.LocalCohomology.colimitClosedSupportComparison_isIso` — the comparison is an
  isomorphism.
* `Stacks.LocalCohomology.isColimitClosedSupportSectionsCocone` — the complexes of
  closed-support sections of a complex have the complex of `T`-supported sections as their
  filtered colimit.
* `Stacks.LocalCohomology.isColimitClosedSupportCoconeOfKInjective` — the stronger statement
  that the canonical cocone *is* a colimit cocone, for a K-injective complex.
* `Stacks.LocalCohomology.localCohomologyWithSupportInIsoOfKInjective` — for a K-injective
  complex, local cohomology with support in `S` is the cohomology of the complex of
  `S`-supported sections.
* `Stacks.LocalCohomology.preservesColimitsOfShape_homologyFunctor_of_exact` — cohomology of
  cochain complexes commutes with colimits of a shape whose colimits are exact (the
  general-shape form of the `ℕ`-indexed
  `Stacks.LocalCohomology.preservesColimitsOfShape_homologyFunctor`).

## Implementation notes

The source argues with a K-injective representative `J` of `K`: there `RH^0_T` is computed by
`H^0_T(J^\bullet) = colim_Z H^0_Z(J^\bullet)`, and filtered colimits being exact, cohomology
passes through the colimit. The formalization follows this literally. The unbounded total right
derived functor is `Stacks.LocalCohomology.derivedSectionsWithSupportIn`, whose canonical unit
`Stacks.LocalCohomology.derivedSectionsWithSupportInUnit` is invertible on a K-injective complex;
the filtered colimit of complexes is checked degreewise, where it is the statement that a section
supported in `T` is supported in the zero locus of its own annihilator; and `H^i` commutes with
the colimit because filtered colimits of modules are exact.

Neither Noetherianity nor stability under specialization is used: the degree-zero sections with
support in `T` are *defined* as the union over the closed subsets of `T`, so the identity
`H^0_T = colim_Z H^0_Z` holds for an arbitrary subset of the spectrum, and the unbounded derived
functor exists for an arbitrary commutative ring because every complex of modules admits a
K-injective resolution. The two hypotheses are therefore carried but unused, as the source's
surrounding section assumes them throughout.

The module universe is `max u v`, matching the folded support-section functor; the index
category lives in the ring's universe `u`, so the exactness of its colimits in
`ModuleCat.{max u v} A` is obtained from AB5 for abelian groups by universe shrinking rather
than from Mathlib's `AB5 (ModuleCat.{u} A)` instance.

## References

* [Stacks Project, Tag 0EF1](https://stacks.math.columbia.edu/tag/0EF1)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard IsFiltered.isConnected

universe u v

namespace Stacks.LocalCohomology

variable (A : Type u) [CommRing A]

/-- Ideals whose zero loci lie in `T`, ordered by reverse inclusion of ideals. Every arrow
therefore induces an inclusion of the corresponding closed supports. -/
abbrev ClosedSupportIdeal (T : Set (PrimeSpectrum A)) :=
  OrderDual { I : Ideal A // PrimeSpectrum.zeroLocus (I : Set A) ⊆ T }

/-- Closed supports contained in `T` form a filtered index category. -/
instance closedSupportIdeal_isFiltered (T : Set (PrimeSpectrum A)) :
    IsFiltered (ClosedSupportIdeal A T) where
  nonempty := ⟨OrderDual.toDual ⟨⊤, by simp⟩⟩
  cocone_objs J J' := by
    let L : ClosedSupportIdeal A T := OrderDual.toDual
      ⟨(OrderDual.ofDual J).1 ⊓ (OrderDual.ofDual J').1, by
        rw [PrimeSpectrum.zeroLocus_inf]
        exact Set.union_subset (OrderDual.ofDual J).2 (OrderDual.ofDual J').2⟩
    exact ⟨L, homOfLE (inf_le_left : (OrderDual.ofDual L).1 ≤ (OrderDual.ofDual J).1),
      homOfLE (inf_le_right : (OrderDual.ofDual L).1 ≤ (OrderDual.ofDual J').1), trivial⟩
  cocone_maps _ _ _ _ := ⟨_, 𝟙 _, Subsingleton.elim _ _⟩

/-- The closed support attached to an index. -/
abbrev ClosedSupportIdeal.support {T : Set (PrimeSpectrum A)} (J : ClosedSupportIdeal A T) :
    Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus ((OrderDual.ofDual J).1 : Set A)

/-- Enlarging the support enlarges the submodule of supported sections. -/
theorem sectionsWithSupportIn_mono {S T : Set (PrimeSpectrum A)} (h : S ⊆ T)
    (M : Type v) [AddCommGroup M] [Module A M] :
    sectionsWithSupportIn A S M ≤ sectionsWithSupportIn A T M := by
  unfold sectionsWithSupportIn
  exact iSup_le fun I ↦ iSup_le fun hI ↦
    le_iSup_of_le I (le_iSup_of_le (hI.trans h) le_rfl)

/-- The component at `M` of the inclusion of supported sections. -/
def sectionsWithSupportInInclusionHom {S T : Set (PrimeSpectrum A)} (h : S ⊆ T)
    (M : ModuleCat.{max u v} A) :
    ModuleCat.of A (sectionsWithSupportIn A S M) ⟶
      ModuleCat.of A (sectionsWithSupportIn A T M) :=
  ModuleCat.ofHom (Submodule.inclusion (sectionsWithSupportIn_mono.{u, max u v} A h M))

/-- The inclusion of supported sections is the identity on underlying elements. -/
@[simp]
theorem sectionsWithSupportInInclusionHom_val {S T : Set (PrimeSpectrum A)} (h : S ⊆ T)
    (M : ModuleCat.{max u v} A) (x : sectionsWithSupportIn A S M) :
    ((sectionsWithSupportInInclusionHom.{u, v} A h M).hom x).val = x.val :=
  Submodule.coe_inclusion (sectionsWithSupportIn_mono.{u, max u v} A h M) x

/-- Inclusion of sections supported in `S` into sections supported in `T`. This is the literal
inclusion of submodules, so its underlying map sends `x` to `x`. -/
def sectionsWithSupportInInclusion {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) :
    sectionsWithSupportInFunctor.{u, v} A S ⟶ sectionsWithSupportInFunctor.{u, v} A T where
  app M := sectionsWithSupportInInclusionHom.{u, v} A h M
  naturality {M N} f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ Subtype.ext ?_)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact ((sectionsWithSupportInInclusionHom_val.{u, v} A h N _).trans
      (sectionsWithSupportInFunctor_map_val A S f x)).trans
      ((sectionsWithSupportInFunctor_map_val A T f _).trans
        (congrArg f.hom (sectionsWithSupportInInclusionHom_val.{u, v} A h M x))).symm

/-- The inclusion along `T ⊆ T` is the identity. -/
@[simp]
theorem sectionsWithSupportInInclusion_refl (T : Set (PrimeSpectrum A)) :
    sectionsWithSupportInInclusion.{u, v} A (Set.Subset.refl T) = 𝟙 _ := by
  ext M x
  exact Subtype.ext (sectionsWithSupportInInclusionHom_val.{u, v} A (Set.Subset.refl T) M x)

/-- The inclusions of supported sections compose. -/
@[simp]
theorem sectionsWithSupportInInclusion_trans {S T U : Set (PrimeSpectrum A)}
    (h : S ⊆ T) (h' : T ⊆ U) :
    sectionsWithSupportInInclusion.{u, v} A h ≫ sectionsWithSupportInInclusion.{u, v} A h' =
      sectionsWithSupportInInclusion.{u, v} A (h.trans h') := by
  ext M x
  exact Subtype.ext ((sectionsWithSupportInInclusionHom_val.{u, v} A h' M _).trans
    ((sectionsWithSupportInInclusionHom_val.{u, v} A h M x).trans
      (sectionsWithSupportInInclusionHom_val.{u, v} A (h.trans h') M x).symm))

/-- The canonical comparison of derived sections for an inclusion of supports, obtained by
deriving the inclusion of the degree-zero section submodules. -/
def derivedSectionsWithSupportInInclusion {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) :
    derivedSectionsWithSupportIn.{u, v} A S ⟶ derivedSectionsWithSupportIn.{u, v} A T :=
  Functor.rightDerivedNatTrans _ _
    (derivedSectionsWithSupportInUnit.{u, v} A S) (derivedSectionsWithSupportInUnit.{u, v} A T)
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))
    (whiskerRight ((sectionsWithSupportInInclusion.{u, v} A h).mapHomotopyCategory
      (ComplexShape.up ℤ)) DerivedCategory.Qh)

/-- The comparison is characterized by compatibility with the canonical derived units. -/
@[reassoc]
theorem derivedSectionsWithSupportInInclusion_fac {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) :
    derivedSectionsWithSupportInUnit.{u, v} A S ≫
        whiskerLeft DerivedCategory.Qh (derivedSectionsWithSupportInInclusion A h) =
      whiskerRight ((sectionsWithSupportInInclusion.{u, v} A h).mapHomotopyCategory
        (ComplexShape.up ℤ)) DerivedCategory.Qh ≫ derivedSectionsWithSupportInUnit A T :=
  Functor.rightDerivedNatTrans_fac _ _ _ _ _ _

/-- The derived comparison along `T ⊆ T` is the identity. -/
@[simp]
theorem derivedSectionsWithSupportInInclusion_refl (T : Set (PrimeSpectrum A)) :
    derivedSectionsWithSupportInInclusion.{u, v} A (Set.Subset.refl T) = 𝟙 _ := by
  simp [derivedSectionsWithSupportInInclusion]

/-- The derived comparisons compose. -/
@[simp, reassoc]
theorem derivedSectionsWithSupportInInclusion_trans {S T U : Set (PrimeSpectrum A)}
    (h : S ⊆ T) (h' : T ⊆ U) :
    derivedSectionsWithSupportInInclusion.{u, v} A h ≫
        derivedSectionsWithSupportInInclusion A h' =
      derivedSectionsWithSupportInInclusion A (h.trans h') := by
  unfold derivedSectionsWithSupportInInclusion
  rw [Functor.rightDerivedNatTrans_comp]
  congr 1
  rw [← whiskerRight_comp, ← NatTrans.mapHomotopyCategory_comp,
    sectionsWithSupportInInclusion_trans]

/-- Local cohomology for the closed supports `V(I) ⊆ T`, as a diagram of functors. Each stage
uses the total right derived functor of sections with that closed support; each transition is
induced by the inclusion of supports. -/
@[implicit_reducible]
def closedSupportCohomologyDiagram (T : Set (PrimeSpectrum A)) (i : ℤ) :
    ClosedSupportIdeal A T ⥤
      (DerivedCategory (ModuleCat.{max u v} A) ⥤ ModuleCat.{max u v} A) where
  obj J := derivedSectionsWithSupportIn.{u, v} A (ClosedSupportIdeal.support A J) ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i
  map {J J'} f := whiskerRight
    (derivedSectionsWithSupportInInclusion A (PrimeSpectrum.zeroLocus_anti_mono_ideal
      (show (OrderDual.ofDual J').1 ≤ (OrderDual.ofDual J).1 from leOfHom f)))
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i)
  map_id J := by
    simp only [derivedSectionsWithSupportInInclusion_refl]
    exact whiskerRight_id' _
  map_comp f g := by
    rw [← whiskerRight_comp, derivedSectionsWithSupportInInclusion_trans]

/-- The closed-support diagram, functorial in the derived object `K`. -/
@[implicit_reducible]
def closedSupportDiagram (T : Set (PrimeSpectrum A)) (i : ℤ) :
    DerivedCategory (ModuleCat.{max u v} A) ⥤
      (ClosedSupportIdeal A T ⥤ ModuleCat.{max u v} A) :=
  (closedSupportCohomologyDiagram.{u, v} A T i).flip

/-- A stage is local cohomology with the indicated closed support. -/
@[simp]
theorem closedSupportDiagram_obj_obj (T : Set (PrimeSpectrum A)) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (J : ClosedSupportIdeal A T) :
    ((closedSupportDiagram.{u, v} A T i).obj K).obj J =
      localCohomologyWithSupportIn A (ClosedSupportIdeal.support A J) K i := rfl

/-- Transitions in the diagram are the canonical inclusion-induced maps on cohomology. -/
@[simp]
theorem closedSupportDiagram_obj_map (T : Set (PrimeSpectrum A)) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{max u v} A)) {J J' : ClosedSupportIdeal A T} (f : J ⟶ J') :
    ((closedSupportDiagram.{u, v} A T i).obj K).map f =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
        ((derivedSectionsWithSupportInInclusion A
          (PrimeSpectrum.zeroLocus_anti_mono_ideal (leOfHom f))).app K) := rfl

/-- Functoriality in the derived object is the usual action on closed-support cohomology. -/
@[simp]
theorem closedSupportDiagram_map_app (T : Set (PrimeSpectrum A)) (i : ℤ)
    {K L : DerivedCategory (ModuleCat.{max u v} A)} (f : K ⟶ L) (J : ClosedSupportIdeal A T) :
    ((closedSupportDiagram.{u, v} A T i).map f).app J =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
        ((derivedSectionsWithSupportIn A (ClosedSupportIdeal.support A J)).map f) := rfl

/-- The canonical map from a closed-support stage to local cohomology with support in `T`. -/
@[implicit_reducible]
def closedSupportStageComparison (T : Set (PrimeSpectrum A)) (i : ℤ)
    (J : ClosedSupportIdeal A T) :
    (closedSupportCohomologyDiagram.{u, v} A T i).obj J ⟶
      derivedSectionsWithSupportIn.{u, v} A T ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i :=
  whiskerRight (derivedSectionsWithSupportInInclusion A (OrderDual.ofDual J).2)
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i)

/-- The stage comparisons respect inclusions of closed supports. -/
@[reassoc (attr := simp)]
theorem closedSupportStageComparison_naturality (T : Set (PrimeSpectrum A)) (i : ℤ)
    {J J' : ClosedSupportIdeal A T} (f : J ⟶ J') :
    (closedSupportCohomologyDiagram.{u, v} A T i).map f ≫
        closedSupportStageComparison A T i J' = closedSupportStageComparison A T i J := by
  dsimp [closedSupportCohomologyDiagram, closedSupportStageComparison]
  rw [← whiskerRight_comp, derivedSectionsWithSupportInInclusion_trans]

/-- The canonical cocone of closed-support local cohomology mapping to support in `T`. -/
@[implicit_reducible]
def closedSupportCocone (T : Set (PrimeSpectrum A)) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    Cocone ((closedSupportDiagram.{u, v} A T i).obj K) where
  pt := (derivedSectionsWithSupportIn.{u, v} A T ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj K
  ι :=
    { app := fun J ↦ (closedSupportStageComparison A T i J).app K
      naturality := fun J J' f ↦ by
        change ((closedSupportCohomologyDiagram A T i).map f).app K ≫
            (closedSupportStageComparison A T i J').app K =
          (closedSupportStageComparison A T i J).app K ≫ 𝟙 _
        rw [Category.comp_id]
        exact congrArg (fun α ↦ α.app K)
          (closedSupportStageComparison_naturality A T i f) }

/-- The comparison induced by the canonical closed-support cocone. It is natural in `K`. -/
@[implicit_reducible]
def colimitClosedSupportComparison (T : Set (PrimeSpectrum A)) (i : ℤ) :
    closedSupportDiagram.{u, v} A T i ⋙ colim ⟶
      derivedSectionsWithSupportIn.{u, v} A T ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i where
  app K := colimit.desc _ (closedSupportCocone A T i K)
  naturality {K L} f := by
    refine colimit.hom_ext fun J ↦ ?_
    change colimit.ι _ J ≫ colim.map ((closedSupportDiagram A T i).map f) ≫
        colimit.desc _ (closedSupportCocone A T i L) =
      colimit.ι _ J ≫ colimit.desc _ (closedSupportCocone A T i K) ≫ _
    rw [colimit.ι_map_assoc, colimit.ι_desc, colimit.ι_desc_assoc]
    exact (closedSupportStageComparison A T i J).naturality f

/-- The colimit comparison agrees with the prescribed inclusion-induced map on every stage. -/
@[reassoc (attr := simp)]
theorem colimit_ι_colimitClosedSupportComparison (T : Set (PrimeSpectrum A)) (i : ℤ)
    (K : DerivedCategory (ModuleCat.{max u v} A)) (J : ClosedSupportIdeal A T) :
    colimit.ι ((closedSupportDiagram.{u, v} A T i).obj K) J ≫
        (colimitClosedSupportComparison A T i).app K =
      (closedSupportStageComparison A T i J).app K :=
  colimit.ι_desc _ _

section Square

variable {C : Type*} [Category* C]

/-- A commuting square whose vertical maps are isomorphisms transfers to the inverses: if
`a ≫ f = g ≫ a'` and `g ≫ t' = t ≫ m`, then `f ≫ a'.inv ≫ t'` and `(a.inv ≫ t) ≫ m` agree. -/
lemma comp_inv_comp_eq_of_square {P Q P' Q' R R' : C} (a : P ≅ Q) (a' : P' ≅ Q')
    (f : Q ⟶ Q') (g : P ⟶ P') (t : P ⟶ R) (t' : P' ⟶ R') (m : R ⟶ R')
    (h₁ : a.hom ≫ f = g ≫ a'.hom) (h₂ : g ≫ t' = t ≫ m) :
    f ≫ a'.inv ≫ t' = (a.inv ≫ t) ≫ m := by
  rw [← cancel_epi a.hom, Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% h₁,
    Iso.hom_inv_id_assoc, h₂]

end Square

section Generic

variable {C : Type*} [Category* C] [Abelian C]

/-- Cohomology of cochain complexes commutes with colimits of shape `J` when colimits of shape
`J` are exact. This is the general-shape form of
`Stacks.LocalCohomology.preservesColimitsOfShape_homologyFunctor`, which is stated for `ℕ`. -/
lemma preservesColimitsOfShape_homologyFunctor_of_exact {J : Type*} [Category* J]
    [HasColimitsOfShape J C] [HasExactColimitsOfShape J C] (i : ℤ) :
    PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) i) :=
  have := CochainComplex.Kunneth.preservesColimitsOfShape_shortComplexFunctor (A := C) (J := J) i
  have := Stacks.HomologyColimit.preservesColimitsOfShape_shortComplex_homologyFunctor
    (A := C) (J := J)
  preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso C (ComplexShape.up ℤ) i).symm

end Generic

/-- Filtered colimits of modules are exact, at any index universe below the module universe. -/
theorem hasExactColimitsOfShape_moduleCat (J : Type u) [SmallCategory J] [IsFiltered J] :
    HasExactColimitsOfShape J (ModuleCat.{max u v} A) :=
  have : AB5OfSize.{u, u} AddCommGrpCat.{max u v} :=
    AB5OfSize_of_univLE.{_, _, max u v, max u v} _
  HasExactColimitsOfShape.domain_of_functor J (forget₂ (ModuleCat A) AddCommGrpCat.{max u v})

/-- A cocone of a filtered diagram of modules whose coprojections are injective and jointly
surjective is a colimit cocone. -/
def isColimit_of_injective_of_jointly_surjective {J : Type u} [SmallCategory J]
    [IsFiltered J] (D : J ⥤ ModuleCat.{max u v} A) (c : Cocone D)
    (hinj : ∀ j, Function.Injective (c.ι.app j).hom)
    (hsurj : ∀ x : c.pt, ∃ (j : J) (y : D.obj j), (c.ι.app j).hom y = x) :
    IsColimit c := by
  have := hasExactColimitsOfShape_moduleCat.{u, v} A J
  have hmono : Mono (colimit.desc D c) := by
    have : ∀ j, Mono (c.ι.app j) := fun j => (ModuleCat.mono_iff_injective _).2 (hinj j)
    have : Mono c.ι := NatTrans.mono_of_mono_app _
    exact colim.map_mono' c.ι (colimit.isColimit D) (isColimitConstCocone J c.pt)
      (colimit.desc D c) (fun j => by
        change colimit.ι D j ≫ colimit.desc D c = c.ι.app j ≫ 𝟙 c.pt
        exact (colimit.ι_desc c j).trans (Category.comp_id _).symm)
  have hepi : Epi (colimit.desc D c) := by
    rw [ModuleCat.epi_iff_surjective]
    intro x
    obtain ⟨j, y, hy⟩ := hsurj x
    refine ⟨(colimit.ι D j).hom y, ?_⟩
    rw [← hy]
    exact congrArg (fun (f : D.obj j ⟶ c.pt) => f.hom y) (colimit.ι_desc c j)
  have hiso : IsIso ((colimit.isColimit D).desc c) := isIso_of_mono_of_epi (colimit.desc D c)
  exact (colimit.isColimit D).ofPointIso

section Colimit

variable {A}

/-- Sections with support in the closed subsets `V(I) ⊆ T`, as a diagram of functors on
cochain complexes. -/
def closedSupportSectionsFunctorDiagram (T : Set (PrimeSpectrum A)) :
    ClosedSupportIdeal A T ⥤
      (CochainComplex (ModuleCat.{max u v} A) ℤ ⥤ CochainComplex (ModuleCat.{max u v} A) ℤ) where
  obj J := Functor.mapHomologicalComplex
    (sectionsWithSupportInFunctor.{u, v} A (ClosedSupportIdeal.support A J)) (ComplexShape.up ℤ)
  map {_J _J'} f := NatTrans.mapHomologicalComplex
    (sectionsWithSupportInInclusion.{u, v} A
      (PrimeSpectrum.zeroLocus_anti_mono_ideal (leOfHom f))) (ComplexShape.up ℤ)
  map_id J :=
    (congrArg (fun α ↦ NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))
      (sectionsWithSupportInInclusion_refl.{u, v} A (ClosedSupportIdeal.support A J))).trans
      (NatTrans.mapHomologicalComplex_id _ _)
  map_comp _f _g :=
    (congrArg (fun α ↦ NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))
      (sectionsWithSupportInInclusion_trans.{u, v} A _ _).symm).trans
      (NatTrans.mapHomologicalComplex_comp _ _ _)

/-- The inclusions of the closed-support section functors into the `T`-support section functor,
as a cocone of functors on cochain complexes. -/
def closedSupportSectionsFunctorCocone (T : Set (PrimeSpectrum A)) :
    Cocone (closedSupportSectionsFunctorDiagram.{u, v} T) where
  pt := Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
    (ComplexShape.up ℤ)
  ι :=
    { app := fun J ↦ NatTrans.mapHomologicalComplex
        (sectionsWithSupportInInclusion.{u, v} A (OrderDual.ofDual J).2) (ComplexShape.up ℤ)
      naturality := fun J J' f ↦ by
        change NatTrans.mapHomologicalComplex (sectionsWithSupportInInclusion.{u, v} A
            (PrimeSpectrum.zeroLocus_anti_mono_ideal (leOfHom f))) (ComplexShape.up ℤ) ≫
            NatTrans.mapHomologicalComplex (sectionsWithSupportInInclusion.{u, v} A
              (OrderDual.ofDual J').2) (ComplexShape.up ℤ) =
          NatTrans.mapHomologicalComplex (sectionsWithSupportInInclusion.{u, v} A
            (OrderDual.ofDual J).2) (ComplexShape.up ℤ) ≫ 𝟙 _
        rw [Category.comp_id]
        exact ((NatTrans.mapHomologicalComplex_comp (ComplexShape.up ℤ) _ _).symm.trans
          (congrArg (fun α ↦ NatTrans.mapHomologicalComplex α (ComplexShape.up ℤ))
            (sectionsWithSupportInInclusion_trans.{u, v} A _ _))) }

/-- The closed-support section complexes of a fixed cochain complex `K`. -/
abbrev closedSupportSectionsDiagram (T : Set (PrimeSpectrum A))
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    ClosedSupportIdeal A T ⥤ CochainComplex (ModuleCat.{max u v} A) ℤ :=
  closedSupportSectionsFunctorDiagram.{u, v} T ⋙
    (evaluation (CochainComplex (ModuleCat.{max u v} A) ℤ)
      (CochainComplex (ModuleCat.{max u v} A) ℤ)).obj K

/-- The canonical cocone exhibiting sections with support in `T` as the colimit of sections with
support in the closed subsets of `T`. -/
def closedSupportSectionsCocone (T : Set (PrimeSpectrum A))
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    Cocone (closedSupportSectionsDiagram.{u, v} T K) :=
  ((evaluation (CochainComplex (ModuleCat.{max u v} A) ℤ)
    (CochainComplex (ModuleCat.{max u v} A) ℤ)).obj K).mapCocone
      (closedSupportSectionsFunctorCocone.{u, v} T)

/-- The coprojections of the closed-support cocone are the inclusions of supported sections. -/
@[simp]
theorem closedSupportSectionsCocone_ι_app (T : Set (PrimeSpectrum A))
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) (J : ClosedSupportIdeal A T) :
    (closedSupportSectionsCocone.{u, v} T K).ι.app J =
      (NatTrans.mapHomologicalComplex (sectionsWithSupportInInclusion.{u, v} A
        (OrderDual.ofDual J).2) (ComplexShape.up ℤ)).app K := rfl

/-- Sections with support in `T` are the filtered colimit of sections with support in the closed
subsets of `T`. In each degree the coprojections are inclusions of submodules, hence injective,
and every section supported in `T` already lies in the sections supported in the zero locus of
its own annihilator, which is a closed subset of `T`. -/
def isColimitClosedSupportSectionsCocone (T : Set (PrimeSpectrum A))
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    IsColimit (closedSupportSectionsCocone.{u, v} T K) := by
  refine HomologicalComplex.isColimitOfEval _ _ (fun n ↦ ?_)
  refine isColimit_of_injective_of_jointly_surjective.{u, v} A _ _ (fun J ↦ ?_) (fun x ↦ ?_)
  · exact Submodule.inclusion_injective
      (sectionsWithSupportIn_mono.{u, max u v} A (OrderDual.ofDual J).2 (K.X n))
  · have hsub : PrimeSpectrum.zeroLocus
        ((Ideal.torsionOf A (K.X n) x.val : Ideal A) : Set A) ⊆ T :=
      (mem_sectionsWithSupportIn_iff A T _ x.val).1 x.property
    refine ⟨OrderDual.toDual ⟨Ideal.torsionOf A (K.X n) x.val, hsub⟩,
      ⟨x.val, (mem_sectionsWithSupportIn_iff A (PrimeSpectrum.zeroLocus
        ((Ideal.torsionOf A (K.X n) x.val : Ideal A) : Set A)) _ x.val).2 (subset_refl _)⟩, ?_⟩
    exact Subtype.ext (sectionsWithSupportInInclusionHom_val.{u, v} A hsub (K.X n) _)

end Colimit

section KInjective

variable {A}

/-- Every cochain complex of modules admits a quasi-isomorphism to a K-injective complex. -/
theorem exists_quasiIso_isKInjective_moduleCat (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    ∃ (I : CochainComplex (ModuleCat.{max u v} A) ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f := by
  obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
  exact ⟨I, q, hI, hq⟩

/-- On a K-injective complex the canonical comparison from supported sections to their total
right derived functor is invertible. -/
instance isIso_derivedSectionsWithSupportInUnit_app (S : Set (PrimeSpectrum A))
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) [K.IsKInjective] :
    IsIso ((derivedSectionsWithSupportInUnit.{u, v} A S).app
      ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
    ((sectionsWithSupportInFunctor.{u, v} A S).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) exists_quasiIso_isKInjective_moduleCat).2
    DerivedCategory.Qh (derivedSectionsWithSupportIn.{u, v} A S)
    (derivedSectionsWithSupportInUnit.{u, v} A S) K inferInstance

/-- For a K-injective complex `K`, local cohomology with support in `S` is the cohomology of the
complex of `S`-supported sections of `K`. -/
def localCohomologyWithSupportInIsoOfKInjective (S : Set (PrimeSpectrum A)) (i : ℤ)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) [K.IsKInjective] :
    localCohomologyWithSupportIn A S
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K)) i ≅
      ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A S)
        (ComplexShape.up ℤ)).obj K).homology i :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
      (asIso ((derivedSectionsWithSupportInUnit.{u, v} A S).app
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K))).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app
        ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A S)
          (ComplexShape.up ℤ)).obj K)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) i).app
      ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A S)
        (ComplexShape.up ℤ)).obj K)

/-- The localization comparison for complexes of supported sections, before any inversion: the
square formed by the inclusion of supported sections, the identification of `Qh ∘ quotient` with
`Q`, and the identification of derived-category cohomology with complex cohomology. -/
private theorem homologyFunctor_map_quotientCompQhIso_square
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) (i : ℤ)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
            (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (sectionsWithSupportInInclusion.{u, v} A h)
              (ComplexShape.up ℤ)).app K))) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
            ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).hom.app
              ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
                (ComplexShape.up ℤ)).obj K)) ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) i).hom.app
            ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
              (ComplexShape.up ℤ)).obj K) =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
          ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).hom.app
            ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A S)
              (ComplexShape.up ℤ)).obj K)) ≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) i).hom.app
            ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A S)
              (ComplexShape.up ℤ)).obj K) ≫
          HomologicalComplex.homologyMap
            ((NatTrans.mapHomologicalComplex (sectionsWithSupportInInclusion.{u, v} A h)
              (ComplexShape.up ℤ)).app K) i := by
  rw [← Functor.map_comp_assoc, DerivedCategory.quotientCompQhIso_hom_naturality,
    Functor.map_comp_assoc, DerivedCategory.homologyFunctorFactors_hom_naturality]
  rfl

/-- The `hom` of the K-injective comparison, written out. -/
theorem localCohomologyWithSupportInIsoOfKInjective_hom (S : Set (PrimeSpectrum A)) (i : ℤ)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) [K.IsKInjective] :
    (localCohomologyWithSupportInIsoOfKInjective.{u, v} S i K).hom =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
        (CategoryTheory.inv ((derivedSectionsWithSupportInUnit.{u, v} A S).app
          ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K))) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).hom.app
          ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A S)
            (ComplexShape.up ℤ)).obj K)) ≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) i).hom.app
        ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A S)
          (ComplexShape.up ℤ)).obj K) := rfl

/-- The square of `homologyFunctor_map_quotientCompQhIso_square`, bracketed for use below. -/
private theorem homologyFunctor_map_quotientCompQhIso_square'
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) (i : ℤ)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
          (DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
            (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex (sectionsWithSupportInInclusion.{u, v} A h)
              (ComplexShape.up ℤ)).app K))) ≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
            ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).hom.app
              ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
                (ComplexShape.up ℤ)).obj K)) ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) i).hom.app
            ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A T)
              (ComplexShape.up ℤ)).obj K)) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
            ((DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).hom.app
              ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A S)
                (ComplexShape.up ℤ)).obj K)) ≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} A) i).hom.app
              ((Functor.mapHomologicalComplex (sectionsWithSupportInFunctor.{u, v} A S)
                (ComplexShape.up ℤ)).obj K)) ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (sectionsWithSupportInInclusion.{u, v} A h)
            (ComplexShape.up ℤ)).app K) i :=
  (homologyFunctor_map_quotientCompQhIso_square h i K).trans (Category.assoc _ _ _).symm

/-- The identification of local cohomology of a K-injective complex with the cohomology of the
complex of supported sections is compatible with enlarging the support: this is the content of
the compatibility of the derived comparison maps with the canonical derived units. -/
theorem homologyMap_localCohomologyWithSupportInIsoOfKInjective
    {S T : Set (PrimeSpectrum A)} (h : S ⊆ T) (i : ℤ)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) [K.IsKInjective] :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
        ((derivedSectionsWithSupportInInclusion A h).app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K))) ≫
        (localCohomologyWithSupportInIsoOfKInjective.{u, v} T i K).hom =
      (localCohomologyWithSupportInIsoOfKInjective.{u, v} S i K).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (sectionsWithSupportInInclusion.{u, v} A h)
            (ComplexShape.up ℤ)).app K) i := by
  have key : (derivedSectionsWithSupportInUnit.{u, v} A S).app
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K) ≫
      (derivedSectionsWithSupportInInclusion A h).app
        (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
          (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (sectionsWithSupportInInclusion.{u, v} A h)
            (ComplexShape.up ℤ)).app K)) ≫
        (derivedSectionsWithSupportInUnit.{u, v} A T).app
          ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K) :=
    Functor.rightDerivedNatTrans_app _ _ _ _ _ _ _
  have e1 : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
        ((derivedSectionsWithSupportInUnit.{u, v} A S).app
          ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
        ((derivedSectionsWithSupportInInclusion A h).app
          (DerivedCategory.Qh.obj
            ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K))) =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
          (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (sectionsWithSupportInInclusion.{u, v} A h)
            (ComplexShape.up ℤ)).app K))) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map
        ((derivedSectionsWithSupportInUnit.{u, v} A T).app
          ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K)) :=
    (Functor.map_comp (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i) _ _).symm.trans
      ((congrArg (fun z ↦ (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map z)
          key).trans
        (Functor.map_comp (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i) _ _))
  exact comp_inv_comp_eq_of_square
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
      (asIso ((derivedSectionsWithSupportInUnit.{u, v} A S).app
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K))))
    ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).mapIso
      (asIso ((derivedSectionsWithSupportInUnit.{u, v} A T).app
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K))))
    _ _ _ _ _ e1 (homologyFunctor_map_quotientCompQhIso_square' h i K)

end KInjective

section Main

variable {A}

/-- For a K-injective complex, the closed-support diagram of local cohomology is isomorphic to
the diagram of cohomologies of the complexes of supported sections. -/
def closedSupportDiagramIsoOfKInjective (T : Set (PrimeSpectrum A)) (i : ℤ)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) [K.IsKInjective] :
    (closedSupportDiagram.{u, v} A T i).obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K)) ≅
      closedSupportSectionsDiagram.{u, v} T K ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{max u v} A) (ComplexShape.up ℤ) i :=
  NatIso.ofComponents
    (fun J ↦ localCohomologyWithSupportInIsoOfKInjective.{u, v}
      (ClosedSupportIdeal.support A J) i K)
    (fun {_J _J'} f ↦ homologyMap_localCohomologyWithSupportInIsoOfKInjective
      (PrimeSpectrum.zeroLocus_anti_mono_ideal (leOfHom f)) i K)

/-- **The colimit calculation at a K-injective complex.** For a K-injective complex the canonical
cocone from closed-support local cohomology to local cohomology with support in `T` is a colimit
cocone: the complexes of supported sections form a filtered colimit, and cohomology commutes with
filtered colimits of modules. -/
def isColimitClosedSupportCoconeOfKInjective (T : Set (PrimeSpectrum A)) (i : ℤ)
    (K : CochainComplex (ModuleCat.{max u v} A) ℤ) [K.IsKInjective] :
    IsColimit (closedSupportCocone.{u, v} A T i (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj K))) := by
  have := hasExactColimitsOfShape_moduleCat.{u, v} A (ClosedSupportIdeal A T)
  have hpres := preservesColimitsOfShape_homologyFunctor_of_exact
    (C := ModuleCat.{max u v} A) (J := ClosedSupportIdeal A T) i
  have hc₂ : IsColimit ((HomologicalComplex.homologyFunctor (ModuleCat.{max u v} A)
      (ComplexShape.up ℤ) i).mapCocone (closedSupportSectionsCocone.{u, v} T K)) :=
    isColimitOfPreserves _ (isColimitClosedSupportSectionsCocone.{u, v} T K)
  refine IsColimit.ofIsoColimit
    ((IsColimit.precomposeHomEquiv (closedSupportDiagramIsoOfKInjective.{u, v} T i K) _).symm
      hc₂)
    (Cocone.ext (localCohomologyWithSupportInIsoOfKInjective.{u, v} T i K).symm (fun J ↦ ?_))
  exact (Iso.comp_inv_eq _).mpr
    (homologyMap_localCohomologyWithSupportInIsoOfKInjective (OrderDual.ofDual J).2 i K).symm

/-- **Stacks Project, Tag 0EF1.** For a Noetherian ring `A` and a specialization-stable subset
`T` of its spectrum, the canonical comparison from the filtered colimit of local cohomology with
closed support contained in `T` to the cohomology of derived sections with support in `T` is an
isomorphism, naturally in the derived object. -/
@[stacks 0EF1]
theorem colimitClosedSupportComparison_isIso (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Set (PrimeSpectrum A)) (_hT : StableUnderSpecialization T) (i : ℤ) :
    IsIso (colimitClosedSupportComparison.{u, v} A T i) := by
  have happ : ∀ K : DerivedCategory (ModuleCat.{max u v} A),
      IsIso ((colimitClosedSupportComparison.{u, v} A T i).app K) := by
    intro K
    obtain ⟨L, f, hL, hf⟩ := exists_quasiIso_isKInjective_moduleCat.{u, v}
      (A := A) (DerivedCategory.Q.objPreimage K)
    have := hf
    have := hL
    let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
        (ComplexShape.up ℤ)).obj L) ≅ K :=
      (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app L ≪≫
        (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K
    have hY : IsIso ((colimitClosedSupportComparison.{u, v} A T i).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
          (ComplexShape.up ℤ)).obj L))) :=
      (IsColimit.nonempty_isColimit_iff_isIso_desc (colimit.isColimit _)).1
        ⟨isColimitClosedSupportCoconeOfKInjective.{u, v} T i L⟩
    rw [show (colimitClosedSupportComparison.{u, v} A T i).app K =
        CategoryTheory.inv ((closedSupportDiagram.{u, v} A T i ⋙ colim).map e.hom) ≫
          (colimitClosedSupportComparison.{u, v} A T i).app
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
              (ComplexShape.up ℤ)).obj L)) ≫
          (derivedSectionsWithSupportIn.{u, v} A T ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).map e.hom from
      (IsIso.eq_inv_comp _).mpr
        ((colimitClosedSupportComparison.{u, v} A T i).naturality e.hom)]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Main

end Stacks.LocalCohomology
