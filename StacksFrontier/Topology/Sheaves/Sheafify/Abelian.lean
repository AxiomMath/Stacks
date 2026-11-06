module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-! # Stacks 0085: sheafification of a presheaf of abelian groups

For a topological space `X`, the sheafification of a presheaf of abelian groups exists, is
unique up to unique isomorphism, and its underlying presheaf of sets is the sheafification of
the underlying presheaf of sets. Part 2 records the resulting adjunction.
-/

@[expose] public section

open CategoryTheory

universe u

variable (X : TopCat.{u})

/-- The Grothendieck topology on the opens of `X` in which a covering sieve is one whose
members cover the open. -/
abbrev opensJ : GrothendieckTopology (TopologicalSpace.Opens X) :=
  Opens.grothendieckTopology X

/-- The category of presheaves of abelian groups on `X`. -/
abbrev AbelianPresheafCat : Type _ :=
  CategoryTheory.Functor (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat.{u}

/-- The category of sheaves of abelian groups on `X`. -/
@[sga "4 IV 11.1.2" "special case",
  sga "4 IV 11.1.5" "special case",
  sga "4 Vbis 4.1.0" "partial",
  sga "4½ Arcata 1.6.3" "special case"]
abbrev AbelianSheafCat : Type _ :=
  CategoryTheory.Sheaf (opensJ X) AddCommGrpCat.{u}

/-- The category of presheaves of sets on `X`. -/
@[sga "3 IV 4.3.1" "special case",
  sga "3 IV 4.3.17" "special case",
  sga "4 I 1.2" "special case",
  sga "4 II 6.0" "special case",
  sga "4½ Arcata 1.6.3" "special case"]
abbrev SetPresheafCat : Type _ :=
  CategoryTheory.Functor (TopologicalSpace.Opens X)ᵒᵖ (Type u)

/-- The category of sheaves of sets on `X`. -/
@[sga "3 IV 4.3.1" "special case",
  sga "4 II 2.1" "special case",
  sga "4 IV 0.1" "special case",
  sga "4 IV 2.1",
  sga "4 Vbis 4.1.0" "partial"]
abbrev SetSheafCat : Type _ :=
  CategoryTheory.Sheaf (opensJ X) (Type u)

/-- The forgetful functor from sheaves of abelian groups to presheaves of abelian groups. -/
@[implicit_reducible, sga "4 V 2.4.2" "special case"]
noncomputable def inclusionAbSheafToAbPresheaf :
    AbelianSheafCat X ⥤ AbelianPresheafCat X :=
  CategoryTheory.sheafToPresheaf (opensJ X) AddCommGrpCat.{u}

/-- The forgetful functor from sheaves of sets to presheaves of sets. -/
@[implicit_reducible,
  sga "3 IV 4.3.13" "special case",
  sga "4 IV 10.4.1" "special case",
  sga "4 IV 4.8" "partial"]
noncomputable def inclusionSetSheafToSetPresheaf :
    SetSheafCat X ⥤ SetPresheafCat X :=
  CategoryTheory.sheafToPresheaf (opensJ X) (Type u)

/-- Forgetting the group structure sectionwise, as a functor from presheaves of abelian groups
to presheaves of sets. -/
@[implicit_reducible, sga "4 I 5.8.0" "special case", sga "4 II 6.3.0" "special case"]
noncomputable def forgetAbPresheafToSetPresheaf :
    AbelianPresheafCat X ⥤ SetPresheafCat X :=
  (CategoryTheory.Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget AddCommGrpCat.{u})

/-- The underlying presheaf of sets of a sheaf of abelian groups. -/
@[implicit_reducible]
noncomputable def forgetAbSheafToSetPresheaf :
    AbelianSheafCat X ⥤ SetPresheafCat X :=
  inclusionAbSheafToAbPresheaf X ⋙ forgetAbPresheafToSetPresheaf X

/-- On a morphism `f` of sheaves of abelian groups, `forgetAbSheafToSetPresheaf` is the morphism
of underlying presheaves of sets of the underlying morphism of presheaves of abelian groups. -/
lemma forgetAbSheafToSetPresheaf_map {F G : AbelianSheafCat X} (f : F ⟶ G) :
    (forgetAbSheafToSetPresheaf X).map f =
      (forgetAbPresheafToSetPresheaf X).map ((inclusionAbSheafToAbPresheaf X).map f) := rfl

/-- Sheafification of presheaves of sets. -/
@[implicit_reducible,
  ega "0 3.5.6" "special case",
  ega "0 3.7.1",
  sga "3 IV 4.3.15" "special case",
  sga "3 VIB 8.1" "special case",
  sga "4 II 3.5" "special case"]
noncomputable def setSheafify : SetPresheafCat X ⥤ SetSheafCat X :=
  CategoryTheory.presheafToSheaf (opensJ X) (Type u)

/-- The unit of the set-level sheafification adjunction at `F`, i.e. the canonical map from a
presheaf of sets to its sheafification. -/
@[ega "0 3.7.1" "special case"]
noncomputable abbrev toSetSheafify (F : SetPresheafCat X) :
    F ⟶ (inclusionSetSheafToSetPresheaf X).obj ((setSheafify X).obj F) :=
  (CategoryTheory.sheafificationAdjunction (opensJ X) (Type u)).unit.app F

/-- The underlying presheaf of sets of a presheaf of abelian groups. -/
@[sga "4 I 5.8.0" "special case", sga "4 II 6.3.0" "object assignment of ε^"]
noncomputable abbrev underlyingSetPresheaf (F : AbelianPresheafCat X) : SetPresheafCat X :=
  (forgetAbPresheafToSetPresheaf X).obj F

/-- The set-level sheafification of the underlying presheaf of sets of `F`. -/
noncomputable abbrev setSheafifiedPresheaf (F : AbelianPresheafCat X) : SetPresheafCat X :=
  (inclusionSetSheafToSetPresheaf X).obj ((setSheafify X).obj (underlyingSetPresheaf X F))

/-- Sheafification commutes with the forgetful functor to sets: the underlying presheaf of sets
of the abelian sheafification of `F` is the sheafification of the underlying presheaf of sets. -/
@[sga "3 IV 4.3.16" "special case", sga "4 II 6.4" "special case"]
noncomputable def canonicalSetIso (F : AbelianPresheafCat X) :
    (forgetAbSheafToSetPresheaf X).obj
        ((CategoryTheory.presheafToSheaf (opensJ X) AddCommGrpCat.{u}).obj F) ≅
      setSheafifiedPresheaf X F :=
  (sheafifyComposeIso (opensJ X) (forget AddCommGrpCat.{u}) F).symm

/-- `canonicalSetIso` identifies the abelian sheafification unit with the set-level one. -/
@[sga "3 IV 4.3.16" "special case", sga "4 II 6.4" "special case"]
lemma canonicalSetIso_hom_fac (F : AbelianPresheafCat X) :
    (forgetAbPresheafToSetPresheaf X).map
        ((sheafificationAdjunction (opensJ X) AddCommGrpCat.{u}).unit.app F) ≫
      (canonicalSetIso X F).hom =
    toSetSheafify X (underlyingSetPresheaf X F) :=
  sheafComposeIso_inv_fac (opensJ X) (forget AddCommGrpCat.{u}) F

/-- **(Stacks 0085, Part 1, existence.)** A presheaf of abelian groups `F` on `X` has a
sheafification: a sheaf of abelian groups `Fbar` with a map `F ⟶ Fbar` whose underlying map of
presheaves of sets exhibits `Fbar` as the set-level sheafification of `F`. -/
@[stacks 0085]
theorem exists_abelian_sheafification (F : AbelianPresheafCat X) :
    ∃ (Fbar : AbelianSheafCat X) (u : F ⟶ (inclusionAbSheafToAbPresheaf X).obj Fbar)
      (iso : (forgetAbSheafToSetPresheaf X).obj Fbar ≅ setSheafifiedPresheaf X F),
      (forgetAbPresheafToSetPresheaf X).map u ≫ iso.hom =
        toSetSheafify X (underlyingSetPresheaf X F) :=
  ⟨(presheafToSheaf (opensJ X) AddCommGrpCat.{u}).obj F,
   (sheafificationAdjunction (opensJ X) AddCommGrpCat.{u}).unit.app F,
   canonicalSetIso X F,
   canonicalSetIso_hom_fac X F⟩

/-! ### Uniqueness -/

section Uniqueness

variable (F : AbelianPresheafCat X)
  (Fbar : AbelianSheafCat X)
  (u : F ⟶ (inclusionAbSheafToAbPresheaf X).obj Fbar)
  (iso : (forgetAbSheafToSetPresheaf X).obj Fbar ≅ setSheafifiedPresheaf X F)

/-- The lift of `u : F → i(Fbar)` to a morphism from the canonical abelian
sheafification of `F` to `Fbar`. -/
noncomputable def liftAdj :
    (presheafToSheaf (opensJ X) AddCommGrpCat.{u}).obj F ⟶ Fbar :=
  ((sheafificationAdjunction (opensJ X) AddCommGrpCat.{u}).homEquiv F Fbar).symm u

/-- `liftAdj` factors `u` through the sheafification unit. -/
@[ega "0 3.5.3" "partial", ega "0 3.5.6" "partial"]
lemma liftAdj_fac :
    (sheafificationAdjunction (opensJ X) AddCommGrpCat.{u}).unit.app F ≫
      (inclusionAbSheafToAbPresheaf X).map (liftAdj X F Fbar u) = u := by
  have h :=
    ((sheafificationAdjunction (opensJ X) AddCommGrpCat.{u}).homEquiv F Fbar).apply_symm_apply u
  rwa [Adjunction.homEquiv_unit] at h

/-- On underlying presheaves of sets, `liftAdj` is the comparison isomorphism
`canonicalSetIso` followed by `iso.inv`. -/
lemma forget_liftAdj
    (hu : (forgetAbPresheafToSetPresheaf X).map u ≫ iso.hom =
            toSetSheafify X (underlyingSetPresheaf X F)) :
    (forgetAbSheafToSetPresheaf X).map (liftAdj X F Fbar u) =
      (canonicalSetIso X F).hom ≫ iso.inv := by
  have hsheaf : Presheaf.IsSheaf (opensJ X) ((forgetAbSheafToSetPresheaf X).obj Fbar) :=
    ((sheafCompose (opensJ X) (forget AddCommGrpCat.{u})).obj Fbar).property
  have h1 := congrArg (forgetAbPresheafToSetPresheaf X).map (liftAdj_fac X F Fbar u)
  rw [Functor.map_comp, ← forgetAbSheafToSetPresheaf_map] at h1
  have key :
      (canonicalSetIso X F).inv ≫ (forgetAbSheafToSetPresheaf X).map (liftAdj X F Fbar u) =
        iso.inv := by
    refine sheafify_hom_ext (opensJ X) _ _ hsheaf ?_
    have step1 :
        toSetSheafify X (underlyingSetPresheaf X F) ≫ (canonicalSetIso X F).inv =
          (forgetAbPresheafToSetPresheaf X).map
              ((sheafificationAdjunction (opensJ X) AddCommGrpCat.{u}).unit.app F) :=
      (Iso.comp_inv_eq _).mpr (canonicalSetIso_hom_fac X F).symm
    have step2 :
        toSetSheafify X (underlyingSetPresheaf X F) ≫ iso.inv =
          (forgetAbPresheafToSetPresheaf X).map u :=
      (Iso.comp_inv_eq _).mpr hu.symm
    rw [step2, ← Category.assoc, step1]
    exact h1
  rw [← key, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- The lift `liftAdj` is an isomorphism: it is one on underlying presheaves of sets by
`forget_liftAdj`, and `forgetAbSheafToSetPresheaf` reflects isomorphisms. -/
lemma liftAdj_isIso
    (hu : (forgetAbPresheafToSetPresheaf X).map u ≫ iso.hom =
            toSetSheafify X (underlyingSetPresheaf X F)) :
    IsIso (liftAdj X F Fbar u) := by
  have : (inclusionAbSheafToAbPresheaf X).ReflectsIsomorphisms :=
    (fullyFaithfulSheafToPresheaf (opensJ X) AddCommGrpCat.{u}).reflectsIsomorphisms
  have : ((CategoryTheory.Functor.whiskeringRight (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat.{u}
        (Type u)).obj (forget AddCommGrpCat.{u})).ReflectsIsomorphisms := inferInstance
  have : (forgetAbPresheafToSetPresheaf X).ReflectsIsomorphisms := this
  have : (forgetAbSheafToSetPresheaf X).ReflectsIsomorphisms :=
    reflectsIsomorphisms_comp _ _
  have : IsIso ((forgetAbSheafToSetPresheaf X).map (liftAdj X F Fbar u)) := by
    rw [forget_liftAdj X F Fbar u iso hu]
    infer_instance
  exact isIso_of_reflects_iso (liftAdj X F Fbar u) (forgetAbSheafToSetPresheaf X)

end Uniqueness

section UniquenessMain

variable (F : AbelianPresheafCat X)
  (Fbar₁ Fbar₂ : AbelianSheafCat X)
  (u₁ : F ⟶ (inclusionAbSheafToAbPresheaf X).obj Fbar₁)
  (u₂ : F ⟶ (inclusionAbSheafToAbPresheaf X).obj Fbar₂)
  (iso₁ : (forgetAbSheafToSetPresheaf X).obj Fbar₁ ≅ setSheafifiedPresheaf X F)
  (iso₂ : (forgetAbSheafToSetPresheaf X).obj Fbar₂ ≅ setSheafifiedPresheaf X F)

/-- The candidate isomorphism `Fbar₁ ≅ Fbar₂` constructed by composing the
two adjunction lifts. -/
noncomputable def uniqueIso
    (hu₁ : (forgetAbPresheafToSetPresheaf X).map u₁ ≫ iso₁.hom =
            toSetSheafify X (underlyingSetPresheaf X F))
    (hu₂ : (forgetAbPresheafToSetPresheaf X).map u₂ ≫ iso₂.hom =
            toSetSheafify X (underlyingSetPresheaf X F)) :
    Fbar₁ ≅ Fbar₂ :=
  haveI := liftAdj_isIso X F Fbar₁ u₁ iso₁ hu₁
  haveI := liftAdj_isIso X F Fbar₂ u₂ iso₂ hu₂
  (asIso (liftAdj X F Fbar₁ u₁)).symm ≪≫ asIso (liftAdj X F Fbar₂ u₂)

/-- `uniqueIso` is the inverse of the first lift followed by the second lift. -/
private theorem uniqueIso_hom_eq
    (hu₁ : (forgetAbPresheafToSetPresheaf X).map u₁ ≫ iso₁.hom =
            toSetSheafify X (underlyingSetPresheaf X F))
    (hu₂ : (forgetAbPresheafToSetPresheaf X).map u₂ ≫ iso₂.hom =
            toSetSheafify X (underlyingSetPresheaf X F)) :
    haveI := liftAdj_isIso X F Fbar₁ u₁ iso₁ hu₁
    (uniqueIso X F Fbar₁ Fbar₂ u₁ u₂ iso₁ iso₂ hu₁ hu₂).hom =
      CategoryTheory.inv (liftAdj X F Fbar₁ u₁) ≫ liftAdj X F Fbar₂ u₂ := rfl

/-- `uniqueIso` is compatible with the two maps out of `F`. -/
lemma uniqueIso_fac_u
    (hu₁ : (forgetAbPresheafToSetPresheaf X).map u₁ ≫ iso₁.hom =
            toSetSheafify X (underlyingSetPresheaf X F))
    (hu₂ : (forgetAbPresheafToSetPresheaf X).map u₂ ≫ iso₂.hom =
            toSetSheafify X (underlyingSetPresheaf X F)) :
    u₁ ≫ (inclusionAbSheafToAbPresheaf X).map
        (uniqueIso X F Fbar₁ Fbar₂ u₁ u₂ iso₁ iso₂ hu₁ hu₂).hom = u₂ := by
  have := liftAdj_isIso X F Fbar₁ u₁ iso₁ hu₁
  have key : u₁ ≫ (inclusionAbSheafToAbPresheaf X).map (CategoryTheory.inv (liftAdj X F Fbar₁ u₁)) =
      (sheafificationAdjunction (opensJ X) AddCommGrpCat.{u}).unit.app F := by
    rw [Functor.map_inv, IsIso.comp_inv_eq]
    exact (liftAdj_fac X F Fbar₁ u₁).symm
  rw [uniqueIso_hom_eq, Functor.map_comp, ← Category.assoc, key]
  exact liftAdj_fac X F Fbar₂ u₂

/-- `uniqueIso` is compatible with the two identifications of the underlying presheaves of
sets with the set-level sheafification. -/
lemma uniqueIso_fac_iso
    (hu₁ : (forgetAbPresheafToSetPresheaf X).map u₁ ≫ iso₁.hom =
            toSetSheafify X (underlyingSetPresheaf X F))
    (hu₂ : (forgetAbPresheafToSetPresheaf X).map u₂ ≫ iso₂.hom =
            toSetSheafify X (underlyingSetPresheaf X F)) :
    (forgetAbSheafToSetPresheaf X).map
        (uniqueIso X F Fbar₁ Fbar₂ u₁ u₂ iso₁ iso₂ hu₁ hu₂).hom ≫ iso₂.hom = iso₁.hom := by
  have := liftAdj_isIso X F Fbar₁ u₁ iso₁ hu₁
  have hg1 := forget_liftAdj X F Fbar₁ u₁ iso₁ hu₁
  have hg2 := forget_liftAdj X F Fbar₂ u₂ iso₂ hu₂
  have : IsIso ((forgetAbSheafToSetPresheaf X).map (liftAdj X F Fbar₁ u₁)) := by
    rw [hg1]; infer_instance
  rw [uniqueIso_hom_eq, Functor.map_comp, Functor.map_inv, hg2]
  simp [hg1]

end UniquenessMain

/-- **(Stacks 0085, Part 1, uniqueness.)** -/
@[stacks 0085]
theorem unique_abelian_sheafification
    (F : AbelianPresheafCat X)
    (Fbar₁ Fbar₂ : AbelianSheafCat X)
    (u₁ : F ⟶ (inclusionAbSheafToAbPresheaf X).obj Fbar₁)
    (u₂ : F ⟶ (inclusionAbSheafToAbPresheaf X).obj Fbar₂)
    (iso₁ : (forgetAbSheafToSetPresheaf X).obj Fbar₁ ≅ setSheafifiedPresheaf X F)
    (iso₂ : (forgetAbSheafToSetPresheaf X).obj Fbar₂ ≅ setSheafifiedPresheaf X F)
    (hu₁ : (forgetAbPresheafToSetPresheaf X).map u₁ ≫ iso₁.hom =
        toSetSheafify X (underlyingSetPresheaf X F))
    (hu₂ : (forgetAbPresheafToSetPresheaf X).map u₂ ≫ iso₂.hom =
        toSetSheafify X (underlyingSetPresheaf X F)) :
    ∃! (φ : Fbar₁ ≅ Fbar₂),
      u₁ ≫ (inclusionAbSheafToAbPresheaf X).map φ.hom = u₂ ∧
      (forgetAbSheafToSetPresheaf X).map φ.hom ≫ iso₂.hom = iso₁.hom := by
  refine ⟨uniqueIso X F Fbar₁ Fbar₂ u₁ u₂ iso₁ iso₂ hu₁ hu₂,
    ⟨uniqueIso_fac_u X F Fbar₁ Fbar₂ u₁ u₂ iso₁ iso₂ hu₁ hu₂,
      uniqueIso_fac_iso X F Fbar₁ Fbar₂ u₁ u₂ iso₁ iso₂ hu₁ hu₂⟩, ?_⟩
  rintro φ' ⟨_, hφ'2⟩
  apply Iso.ext
  have : (inclusionAbSheafToAbPresheaf X).Faithful :=
    (fullyFaithfulSheafToPresheaf (opensJ X) AddCommGrpCat.{u}).faithful
  have : ((CategoryTheory.Functor.whiskeringRight (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat.{u}
        (Type u)).obj (forget AddCommGrpCat.{u})).Faithful := inferInstance
  have : (forgetAbPresheafToSetPresheaf X).Faithful := this
  have : (forgetAbSheafToSetPresheaf X).Faithful := Functor.Faithful.comp _ _
  apply (forgetAbSheafToSetPresheaf X).map_injective
  have h1 : (forgetAbSheafToSetPresheaf X).map φ'.hom = iso₁.hom ≫ iso₂.inv := by
    rw [← hφ'2]; simp
  have h2 : (forgetAbSheafToSetPresheaf X).map
      (uniqueIso X F Fbar₁ Fbar₂ u₁ u₂ iso₁ iso₂ hu₁ hu₂).hom = iso₁.hom ≫ iso₂.inv := by
    rw [← uniqueIso_fac_iso X F Fbar₁ Fbar₂ u₁ u₂ iso₁ iso₂ hu₁ hu₂]; simp
  rw [h1, h2]

/-! ### Part 2: Adjunction and naturality -/

variable [CategoryTheory.HasSheafify (opensJ X) AddCommGrpCat.{u}]

/-- Sheafification of presheaves of abelian groups, as a functor. -/
@[sga "3 VIB 8.1" "special case"]
noncomputable def sheafifyAb : AbelianPresheafCat X ⥤ AbelianSheafCat X :=
  CategoryTheory.presheafToSheaf (opensJ X) AddCommGrpCat.{u}

/-- Sheafification is left adjoint to the inclusion of sheaves into presheaves. -/
@[sga "3 IV 4.3.16" "Hom(P, special case", sga "4 II 6.4" "left adjoint a_γ to i_γ"]
noncomputable def sheafifyAbAdjunction :
    sheafifyAb X ⊣ inclusionAbSheafToAbPresheaf X :=
  CategoryTheory.sheafificationAdjunction (opensJ X) AddCommGrpCat.{u}

/-- **(Stacks 0085, Part 2.)** The adjunction bijection
`Hom(F^#, G) ≃ Hom(F, G)` defining sheafification of presheaves of abelian groups. -/
@[stacks 0085, sga "3 IV 4.3.16" "Hom(P, special case"]
noncomputable def sheafifyAbHomEquiv (F : AbelianPresheafCat X) (G : AbelianSheafCat X) :
    ((sheafifyAb X).obj F ⟶ G) ≃ (F ⟶ (inclusionAbSheafToAbPresheaf X).obj G) :=
  (sheafifyAbAdjunction X).homEquiv F G

/-- `sheafifyAbHomEquiv` is natural in the presheaf variable. -/
theorem sheafifyAbHomEquiv_naturality_left
    (F F' : AbelianPresheafCat X) (G : AbelianSheafCat X)
    (f : F ⟶ F') (g : (sheafifyAb X).obj F' ⟶ G) :
    sheafifyAbHomEquiv X F G ((sheafifyAb X).map f ≫ g) =
      f ≫ sheafifyAbHomEquiv X F' G g :=
  Adjunction.homEquiv_naturality_left _ _ _

/-- `sheafifyAbHomEquiv` is natural in the sheaf variable. -/
theorem sheafifyAbHomEquiv_naturality_right
    (F : AbelianPresheafCat X) (G G' : AbelianSheafCat X)
    (g : G ⟶ G') (h : (sheafifyAb X).obj F ⟶ G) :
    sheafifyAbHomEquiv X F G' (h ≫ g) =
      sheafifyAbHomEquiv X F G h ≫ (inclusionAbSheafToAbPresheaf X).map g :=
  Adjunction.homEquiv_naturality_right _ _ _

/-- The functor `sheafifyAb` is a sheafification in the sense of Part 1: its unit at `F`
becomes the set-level sheafification map under the forgetful functor to presheaves of sets. -/
@[sga "3 IV 4.3.16" "special case", sga "4 II 6.4" "special case"]
theorem sheafifyAb_unit_underlying_set (F : AbelianPresheafCat X) :
    ∃ (iso : (forgetAbSheafToSetPresheaf X).obj ((sheafifyAb X).obj F) ≅
              setSheafifiedPresheaf X F),
      (forgetAbPresheafToSetPresheaf X).map ((sheafifyAbAdjunction X).unit.app F) ≫ iso.hom =
        toSetSheafify X (underlyingSetPresheaf X F) :=
  ⟨canonicalSetIso X F, canonicalSetIso_hom_fac X F⟩

