module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.PresheafSpectralSequence.FilteredAbutment

/-!
# The abutment of the spectral sequence of a hypercovering of a presheaf is cohomology over `G`

The identification of the abutment of the spectral sequence of a hypercovering `K` of a presheaf
`G` with the right derived functors of the sections functor `Γ(G, -)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Augmented

universe q w v u

namespace Stacks.CategoryTheory.Hypercovering

/-! ### The abutment is cohomology over the presheaf `G` -/

section AbutmentIsCohomology

open CochainComplex StacksDraft.DerivedSectionsComparison Stacks.Cohomology.Leray

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
variable (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})]

/-- **The augmentation of the double complex of a complex of abelian sheaves**: in outer degree
`r` the degree-zero part of `hypercoverPresheafAugmentation` at the `r`-th term.  Its target is the
zeroth row of the double complex on the nose, which is what makes the index bookkeeping of
[Stacks, Tag 0133] disappear: the inner extension by zero is already inside
`SemiRepresentable.sectionsComplexIntFunctor`. -/
def presheafSectionsAug
    (Z : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℤ) :
    ((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z ⟶
      rowZero ((hypercoverPresheafDoubleFunctor J G K).obj Z) where
  f r := augZero ((presheafSectionsFunctor J G K).obj (Z.X r))
    ((SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
      K.toSimplicialObject).obj (Z.X r))
    ((hypercoverPresheafAugmentation J G K).app (Z.X r))
  comm' r r' _ := (augZero_nat (presheafSectionsFunctor J G K)
    (SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
      K.toSimplicialObject)
    ((hypercoverPresheafAugmentation J G K).app)
    (fun {_ _} φ => (hypercoverPresheafAugmentation J G K).naturality φ) (Z.d r r')).symm

omit [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})] in
/-- **The augmentation is natural in the complex of abelian sheaves.** -/
lemma presheafSectionsAug_naturality
    {Z Z' : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℤ}
    (φ : Z ⟶ Z') :
    presheafSectionsAug J G K Z ≫ rowZeroMap ((hypercoverPresheafDoubleFunctor J G K).map φ) =
      ((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℤ)).map φ ≫
        presheafSectionsAug J G K Z' := by
  refine HomologicalComplex.hom_ext _ _ fun r => ?_
  exact (augZero_nat (presheafSectionsFunctor J G K)
    (SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
      K.toSimplicialObject)
    ((hypercoverPresheafAugmentation J G K).app)
    (fun {_ _} ψ => (hypercoverPresheafAugmentation J G K).naturality ψ) (φ.f r)).symm

omit [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})] in
/-- **All four hypotheses of [Stacks, Tag 0133] for the double complex of a bounded below complex
of injective abelian sheaves.**  Finiteness of the antidiagonals comes from the lower bound on the
complex together with the vanishing of the complex of sections in negative degrees; exactness of
the columns away from degree `0` and the degree-zero kernel clause are the two halves of
`quasiIso_hypercoverPresheafAugmentation`, i.e. of [Stacks, Tag 09VW] and [Stacks, Tag 09VV]. -/
theorem hypotheses_presheafSectionsAug
    (Z : CochainComplex (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ℤ)
    (hZ : ∃ n : ℤ, Z.IsStrictlyGE n) (hinj : ∀ n : ℤ, Injective (Z.X n)) :
    Hypotheses
      (((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
      ((hypercoverPresheafDoubleFunctor J G K).obj Z) (presheafSectionsAug J G K Z) := by
  have hz := fun p r (hr : r < 0) =>
    SemiRepresentable.isZero_sectionsComplexIntFunctor_obj_X.{q, w, v, u}
      J.toGrothendieck K.toSimplicialObject (Z.X p) r hr
  have := hinj
  have hq := fun p : ℤ => quasiIso_hypercoverPresheafAugmentation J G K (Z.X p)
  refine
    { diagonalFinite := ?_
      zero_of_neg := hz
      exactAt_of_ne_zero := fun p r hr => ?_
      inducesIsoKernel := fun p => ?_ }
  · obtain ⟨n₀, hn₀⟩ := hZ
    have := hn₀
    intro n
    refine (Set.finite_Icc n₀ n).subset ?_
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    refine Set.mem_Icc.2 ⟨?_, ?_⟩
    · by_contra h
      exact hp ((HomologicalComplex.eval AddCommGrpCat.{max (max u v) (max q w)}
        (ComplexShape.up ℤ) (n - p)).map_isZero
          ((SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
            K.toSimplicialObject).map_isZero
              (Z.isZero_of_isStrictlyGE n₀ p (by omega))))
    · by_contra h
      exact hp (hz p (n - p) (by omega))
  · exact exactAt_of_quasiIso_single _ _ ((hypercoverPresheafAugmentation J G K).app (Z.X p))
      r hr
  · exact ⟨augZero_comp_d _ _ _, isIso_kernelLift_augZero _ _ (hz p (-1) (by omega)) _⟩

/-- **The hypotheses of [Stacks, Tag 0133] at the chosen injective resolution of a sheaf.** -/
theorem hypotheses_presheafSectionsAug_resolution
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    Hypotheses
      (((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj
            (injectiveResolution F).cocomplex))
      (hypercoverPresheafDouble J G K F)
      (presheafSectionsAug J G K ((ComplexShape.embeddingUpNat.extendFunctor
        (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj
          (injectiveResolution F).cocomplex)) :=
  hypotheses_presheafSectionsAug J G K _ (exists_isStrictlyGE_injectiveResolutionExtend F)
    (injective_injectiveResolutionExtend_X F)

/-- `Γ(G, -)` applied to the chosen injective resolution of a sheaf, extended by zero. -/
abbrev presheafSectionsResZ
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    CochainComplex AddCommGrpCat.{max (max u v) (max q w)} ℤ :=
  ((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).obj
        (injectiveResolution F).cocomplex)

/-- The morphism of `Γ`-applied resolutions attached to a morphism of sheaves, via the chosen
descent to the chosen injective resolutions.  Functorial only up to homotopy. -/
def presheafSectionsResZMap
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    presheafSectionsResZ J G K F ⟶ presheafSectionsResZ J G K F' :=
  ((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((ComplexShape.embeddingUpNat.extendFunctor
      (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).map
        (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F)))

/-- A homotopy between two descents to the chosen injective resolutions induces a homotopy of the
induced morphisms of `Γ`-applied extended resolutions: sections are additive and extension by zero
carries homotopies to homotopies. -/
def presheafSectionsResZHomotopy
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}}
    {φ ψ : (injectiveResolution F).cocomplex ⟶ (injectiveResolution F').cocomplex}
    (H : Homotopy φ ψ) :
    Homotopy
      (((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).map φ))
      (((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})).map ψ)) :=
  (presheafSectionsFunctor J G K).mapHomotopy (H.extend ComplexShape.embeddingUpNat)

/-- `presheafSectionsResZMap` sends an identity to the identity in cohomology. -/
lemma homologyMap_presheafSectionsResZMap_id
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) (n : ℤ) :
    HomologicalComplex.homologyMap (presheafSectionsResZMap J G K (𝟙 F)) n = 𝟙 _ := by
  have h := (presheafSectionsResZHomotopy J G K
    (InjectiveResolution.descIdHomotopy F (injectiveResolution F))).homologyMap_eq n
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id] at h
  exact h

/-- `presheafSectionsResZMap` is multiplicative in cohomology. -/
lemma homologyMap_presheafSectionsResZMap_comp
    {F F' F'' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F')
    (g : F' ⟶ F'') (n : ℤ) :
    HomologicalComplex.homologyMap (presheafSectionsResZMap J G K (f ≫ g)) n =
      HomologicalComplex.homologyMap (presheafSectionsResZMap J G K f) n ≫
        HomologicalComplex.homologyMap (presheafSectionsResZMap J G K g) n := by
  have h := (presheafSectionsResZHomotopy J G K
    (InjectiveResolution.descCompHomotopy f g (injectiveResolution F) (injectiveResolution F')
      (injectiveResolution F''))).homologyMap_eq n
  rw [Functor.map_comp, Functor.map_comp, HomologicalComplex.homologyMap_comp] at h
  exact h

/-- **`H^n(Γ(G, I^•(-)))`, as a functor of the sheaf.**  The `Γ`-applied chosen resolution is
functorial only up to homotopy, but cohomology is homotopy invariant. -/
def presheafSectionsResZHomologyFunctor (n : ℕ) :
    Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)} ⥤
      AddCommGrpCat.{max (max u v) (max q w)} where
  obj F := (presheafSectionsResZ J G K F).homology (n : ℤ)
  map f := HomologicalComplex.homologyMap (presheafSectionsResZMap J G K f) (n : ℤ)
  map_id F := homologyMap_presheafSectionsResZMap_id J G K F (n : ℤ)
  map_comp f g := homologyMap_presheafSectionsResZMap_comp J G K f g (n : ℤ)

/-- **[Stacks, Tag 0133] at a sheaf**: `H^n(Γ(G, I^•(F))) ≅ H^n(Tot(A^{•,•}(F)))`, the
isomorphism the comparison map `comparisonMapP` induces on cohomology. -/
def hypercoverPresheafTotalComparisonIso (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (presheafSectionsResZ J G K F).homology (n : ℤ) ≅
      ((hypercoverPresheafDouble J G K F).total (ComplexShape.up ℤ)).homology (n : ℤ) :=
  comparisonHomologyIso _ _ _ (hypotheses_presheafSectionsAug_resolution J G K F) (n : ℤ)

/-- **`H^n(Γ(G, I^•(-))) ≅ H^n(Tot(A^{•,•}(-)))`, naturally in the sheaf.**  At each sheaf this is
`comparisonHomologyIso`, the isomorphism the comparison map of [Stacks, Tag 0133] induces on
cohomology; its naturality is `comparisonMapP_naturality` with cohomology applied to it.  Both are
available because that comparison map is *data* and not a chosen witness of an existential. -/
def hypercoverPresheafTotalComparisonNatIso (n : ℕ) :
    presheafSectionsResZHomologyFunctor J G K n ≅
      hypercoverPresheafFiltrationFunctor J G K (n : ℤ) ⋙
        CategoryTheory.FilteredObject.forget :=
  NatIso.ofComponents (fun F => hypercoverPresheafTotalComparisonIso J G K n F)
    (fun {F F'} f => by
      have hsq := congrArg (fun z => HomologicalComplex.homologyMap z (n : ℤ))
        (comparisonMapP_naturality _ _ _ (hypotheses_presheafSectionsAug_resolution J G K F)
          (hypotheses_presheafSectionsAug_resolution J G K F')
          (presheafSectionsResZMap J G K f)
          (hypercoverPresheafDoubleMap J G K f) (presheafSectionsAug_naturality J G K _))
      simp only [HomologicalComplex.homologyMap_comp] at hsq
      exact hsq.symm)

/-- `Γ(G, -)` applied to the chosen injective resolution of a sheaf, indexed by `ℕ`. -/
abbrev presheafSectionsResNat
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    CochainComplex AddCommGrpCat.{max (max u v) (max q w)} ℕ :=
  ((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (injectiveResolution F).cocomplex

/-- The morphism of `ℕ`-indexed `Γ`-applied resolutions attached to a morphism of sheaves. -/
def presheafSectionsResNatMap
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    presheafSectionsResNat J G K F ⟶ presheafSectionsResNat J G K F' :=
  ((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F))

/-- Piece (a) of the comparison: in the degrees coming from `ℕ`, the cohomology of the
`ℤ`-extension is the cohomology of the original complex. -/
def presheafSectionsResExtendIso (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (presheafSectionsResZ J G K F).homology (n : ℤ) ≅
      (presheafSectionsResNat J G K F).homology n :=
  (extendUpNatMapHomologyNatIso (presheafSectionsFunctor J G K) n).app
    (injectiveResolution F).cocomplex

omit [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})] in
/-- **The homology functor acts on morphisms by `HomologicalComplex.homologyMap`.**  Stated so
that the identification can be used as a rewrite rule rather than left to a definitional
comparison, which is what keeps the naturality proofs below affordable. -/
lemma homologyFunctor_map_eq_homologyMap.{t, s} {D : Type s} [Category.{t} D] [Abelian D]
    {I : Type*} {c : ComplexShape I} {X Y : HomologicalComplex D c} (g : X ⟶ Y) (i : I) :
    (HomologicalComplex.homologyFunctor D c i).map g = HomologicalComplex.homologyMap g i := rfl

/-- `presheafSectionsResZMap` is the action on the chosen descent of the composite of extension by
zero with `Γ(G, -)` applied degreewise. -/
lemma presheafSectionsResZMap_eq
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    presheafSectionsResZMap J G K f =
      (ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ⋙
        (presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F)) := rfl

/-- The cohomology of `presheafSectionsResZMap` in degree `(n : ℤ)` is the action of the composite
of extension by zero, `Γ(G, -)` degreewise and cohomology in degree `(n : ℤ)`.

Proved by rewriting rather than by `rfl`: the two sides have definitionally equal but syntactically
different types, and discovering that by a single definitional comparison does not finish. -/
lemma homologyMap_presheafSectionsResZMap (n : ℕ)
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    HomologicalComplex.homologyMap (presheafSectionsResZMap J G K f) (n : ℤ) =
      (ComplexShape.embeddingUpNat.extendFunctor
          (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ⋙
        (presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
            (ComplexShape.up ℤ) (n : ℤ)).map
          (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F)) := by
  rw [← homologyFunctor_map_eq_homologyMap, Functor.comp_map, Functor.comp_map,
    presheafSectionsResZMap_eq]
  rfl

/-- The cohomology of `presheafSectionsResNatMap` in degree `n` is the action of the composite of
`Γ(G, -)` degreewise and cohomology in degree `n`. -/
lemma homologyMap_presheafSectionsResNatMap (n : ℕ)
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    HomologicalComplex.homologyMap (presheafSectionsResNatMap J G K f) n =
      ((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
          (ComplexShape.up ℕ) n).map
            (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F)) := rfl

/-- `presheafSectionsResExtendIso` is the component of `extendUpNatMapHomologyNatIso` at the chosen
injective resolution. -/
lemma presheafSectionsResExtendIso_hom_eq (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (presheafSectionsResExtendIso J G K n F).hom =
      (extendUpNatMapHomologyNatIso (presheafSectionsFunctor J G K) n).hom.app
        (injectiveResolution F).cocomplex := rfl

/-- The left-hand side of the naturality square of `presheafSectionsResExtendIso`, written in the
composite-functor spelling of `extendUpNatMapHomologyNatIso`. -/
lemma homologyMap_comp_presheafSectionsResExtendIso_hom (n : ℕ)
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    HomologicalComplex.homologyMap (presheafSectionsResZMap J G K f) (n : ℤ) ≫
        (presheafSectionsResExtendIso J G K n F').hom =
      (ComplexShape.embeddingUpNat.extendFunctor
            (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ⋙
          (presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
              (ComplexShape.up ℤ) (n : ℤ)).map
            (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F)) ≫
        (extendUpNatMapHomologyNatIso (presheafSectionsFunctor J G K) n).hom.app
          (injectiveResolution F').cocomplex := by
  rw [homologyMap_presheafSectionsResZMap, presheafSectionsResExtendIso_hom_eq]
  rfl

/-- The right-hand side of the naturality square of `presheafSectionsResExtendIso`, written in the
composite-functor spelling of `extendUpNatMapHomologyNatIso`. -/
lemma presheafSectionsResExtendIso_hom_comp_homologyMap (n : ℕ)
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    (presheafSectionsResExtendIso J G K n F).hom ≫
        HomologicalComplex.homologyMap (presheafSectionsResNatMap J G K f) n =
      (extendUpNatMapHomologyNatIso (presheafSectionsFunctor J G K) n).hom.app
          (injectiveResolution F).cocomplex ≫
        ((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
            (ComplexShape.up ℕ) n).map
              (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F)) := by
  rw [homologyMap_presheafSectionsResNatMap, presheafSectionsResExtendIso_hom_eq]
  rfl

/-- The naturality square of `extendUpNatMapHomologyNatIso` at the chosen descent, in the spelling
in which it is literally `CategoryTheory.NatTrans.naturality`. -/
lemma extendUpNatMapHomologyNatIso_naturality_desc (n : ℕ)
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    (ComplexShape.embeddingUpNat.extendFunctor
            (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) ⋙
          (presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
              (ComplexShape.up ℤ) (n : ℤ)).map
            (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F)) ≫
        (extendUpNatMapHomologyNatIso (presheafSectionsFunctor J G K) n).hom.app
          (injectiveResolution F').cocomplex =
      (extendUpNatMapHomologyNatIso (presheafSectionsFunctor J G K) n).hom.app
          (injectiveResolution F).cocomplex ≫
        ((presheafSectionsFunctor J G K).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
            (ComplexShape.up ℕ) n).map
              (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F)) :=
  (extendUpNatMapHomologyNatIso (presheafSectionsFunctor J G K) n).hom.naturality
    (InjectiveResolution.desc f (injectiveResolution F') (injectiveResolution F))

/-- `presheafSectionsResExtendIso` is natural in the sheaf, for the chosen descent.

The square is pasted from the three preceding lemmas rather than read off
`CategoryTheory.NatTrans.naturality` directly: the definitional comparison between the two
spellings of each of its four corners is affordable one corner at a time and not all at once. -/
lemma presheafSectionsResExtendIso_hom_naturality (n : ℕ)
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    HomologicalComplex.homologyMap (presheafSectionsResZMap J G K f) (n : ℤ) ≫
        (presheafSectionsResExtendIso J G K n F').hom =
      (presheafSectionsResExtendIso J G K n F).hom ≫
        HomologicalComplex.homologyMap (presheafSectionsResNatMap J G K f) n :=
  (homologyMap_comp_presheafSectionsResExtendIso_hom J G K n f).trans
    ((extendUpNatMapHomologyNatIso_naturality_desc J G K n f).trans
      (presheafSectionsResExtendIso_hom_comp_homologyMap J G K n f).symm)

/-- Piece (b) of the comparison: the right derived functor of sections over `G` computed by the
chosen injective resolution. -/
def presheafSectionsResRightDerivedIso (n : ℕ)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) :
    (presheafSectionsResNat J G K F).homology n ≅
      ((presheafSectionsFunctor J G K).rightDerived n).obj F :=
  ((injectiveResolution F).isoRightDerivedObj (presheafSectionsFunctor J G K) n).symm

/-- `presheafSectionsResRightDerivedIso` is natural in the sheaf, for the chosen descent. -/
lemma presheafSectionsResRightDerivedIso_hom_naturality (n : ℕ)
    {F F' : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}} (f : F ⟶ F') :
    HomologicalComplex.homologyMap (presheafSectionsResNatMap J G K f) n ≫
        (presheafSectionsResRightDerivedIso J G K n F').hom =
      (presheafSectionsResRightDerivedIso J G K n F).hom ≫
        ((presheafSectionsFunctor J G K).rightDerived n).map f :=
  (InjectiveResolution.isoRightDerivedObj_inv_naturality f (injectiveResolution F)
    (injectiveResolution F') _
    (InjectiveResolution.desc_commutes_zero f (injectiveResolution F')
      (injectiveResolution F)) (presheafSectionsFunctor J G K) n).symm

/-- **`H^n(Γ(G, I^•(-))) ≅ R^nΓ(G, -)`, naturally in the sheaf.** -/
def presheafSectionsRightDerivedNatIso (n : ℕ) :
    presheafSectionsResZHomologyFunctor J G K n ≅
      (presheafSectionsFunctor J G K).rightDerived n :=
  NatIso.ofComponents
    (fun F => presheafSectionsResExtendIso J G K n F ≪≫
      presheafSectionsResRightDerivedIso J G K n F)
    (fun {F F'} f => by
      dsimp only [presheafSectionsResZHomologyFunctor, Iso.trans_hom]
      rw [← Category.assoc, presheafSectionsResExtendIso_hom_naturality J G K n f,
        Category.assoc, presheafSectionsResRightDerivedIso_hom_naturality J G K n f,
        Category.assoc])

/-- **The convergence half of the spectral sequence clause of [Stacks, Tag 09VX]**: the cohomology
of the total complex, which is what `hypercoverPresheafFunctorialAbutment` abuts to, is
`R^nΓ(G, -)`, naturally in the sheaf. -/
def hypercoverPresheafAbutmentIso (n : ℕ) :
    hypercoverPresheafFiltrationFunctor J G K (n : ℤ) ⋙
        CategoryTheory.FilteredObject.forget ≅
      (presheafSectionsFunctor J G K).rightDerived n :=
  (hypercoverPresheafTotalComparisonNatIso J G K n).symm ≪≫
    presheafSectionsRightDerivedNatIso J G K n

/-- **The functorial filtered abutment of the spectral sequence of `K`, abutting to cohomology
over the presheaf `G`.**  This is the `abutment` field of the spectral sequence clause of
[Stacks, Tag 09VX]: `hypercoverPresheafFunctorialAbutment` with its abutment transported along
`hypercoverPresheafAbutmentIso`. -/
def hypercoverPresheafAbutment :
    FunctorialFirstQuadrantAbutsTo (hypercoverPresheafSpectralSequenceFunctor J G K)
      (fun n => (presheafSectionsFunctor J G K).rightDerived n) :=
  (hypercoverPresheafFunctorialAbutment J G K).ofIsoAbutment
    (hypercoverPresheafAbutmentIso J G K)

end AbutmentIsCohomology

end Stacks.CategoryTheory.Hypercovering

end
