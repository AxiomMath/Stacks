module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionModificationMap
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage

/-!
# The triples with empty closed subset

In the situation of Stacks 0GH8, a morphism `u : V ⟶ U'` from an object of the big fppf site over
`S` determines the triple `(∅, u, ∅ ⟶ W)` of Artin's functor `F`. This file constructs it, as
the triple of `x̃ = u ∘ (U' ⊆ X')` in the sense of the proof of **Stacks 0GHC**: its closed subset
is `|x̃|⁻¹ T'`, which is empty because `x̃` lands in `U'`, its second component is `u`, and its
third is `g ∘ x̃_{/∅}`. For an empty closed subset the compatibility witness of the source,
`V' = V` with `x' = x̃`, does work: every completion along the empty set is the empty sheaf, so
the cartesian square and the completion condition of the witness hold trivially.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.emptyTriple`: the triple `(∅, u, ∅ ⟶ W)`.

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.bot_mem_of_completionSheaf_yoneda`: the
  completion of a representable presheaf along the empty set has sections only over objects
  covered by the empty sieve.
* `AlgebraicGeometry.Artin.ContractionSituation.emptyTriple_Z`: the closed subset of the triple
  is empty.

## References

* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHC](https://stacks.math.columbia.edu/tag/0GHC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An object of the site carrying a section with point-set image in the empty set is covered by
the empty sieve: it has no points. -/
theorem bot_mem_of_hasImageIn_of_eq_empty {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T : Set (Space.points B S hS X)} (hT : T = ∅) {U : BigFppfOver B S hS}
    {x : X.obj (op U)} (hx : Space.HasImageIn B S hS X T U x) :
    (⊥ : Sieve U) ∈ BigFppfOver.topology B S hS U := by
  subst hT
  apply BigFppfOver.bot_mem_topology
  refine ⟨fun s => ?_⟩
  obtain ⟨w, -⟩ := Space.surjective_pointsToScheme B S hS U s
  obtain ⟨p, rfl⟩ := Quot.exists_rep w
  exact hx p

/-- The completion of a representable presheaf along the empty set has sections only over objects
covered by the empty sieve. -/
theorem bot_mem_of_completionSheaf_yoneda {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : Z = ∅) {U : (BigFppfOver B S hS)ᵒᵖ}
    (e : (Space.completionSheaf B S hS (yoneda.obj V) Z).obj.obj U) :
    (⊥ : Sieve U.unop) ∈ BigFppfOver.topology B S hS U.unop :=
  bot_mem_of_hasImageIn_of_eq_empty hZ
    ((Space.completionSheafIsoSubfunctor B S hS (isAlgebraicSpace_yoneda B S hS V).isSheaf
      Z).hom.app U e).2

/-- A sheaf has at most one section over an object carrying a section of the completion of a
representable presheaf along the empty set. -/
private theorem subsingleton_obj_of_completionSheaf_yoneda {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : Z = ∅) {U : (BigFppfOver B S hS)ᵒᵖ}
    (e : (Space.completionSheaf B S hS (yoneda.obj V) Z).obj.obj U)
    (G : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))) : Subsingleton (G.obj.obj U) :=
  Space.subsingleton_of_bot_mem B S hS G.property (bot_mem_of_completionSheaf_yoneda hZ e)

/-- Morphisms out of the completion of a representable presheaf along the empty set agree. -/
theorem completionSheaf_yoneda_hom_ext_of_eq_empty {V : BigFppfOver B S hS}
    {Z : Set (Space.points B S hS (yoneda.obj V))} (hZ : Z = ∅)
    {G : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (φ ψ : Space.completionSheaf B S hS (yoneda.obj V) Z ⟶ G) : φ = ψ := by
  apply Sheaf.hom_ext
  ext U e
  exact (subsingleton_obj_of_completionSheaf_yoneda hZ e G).elim _ _

/-- A morphism into `U'` meets `T'` nowhere: the inverse image of `T'` is empty. -/
theorem preimage_T'_eq_empty {V : BigFppfOver B S hS} (u : yoneda.obj V ⟶ c.U'.toFunctor) :
    Space.pointsMap B S hS (yoneda.obj V) (u ≫ c.U'.ι) ⁻¹' c.T' = ∅ := by
  ext z
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  rw [Space.pointsMap_comp, Function.comp_apply, ← Set.mem_compl_iff,
    ← c.range_pointsMap_ι_U']
  exact ⟨_, rfl⟩

/-- The compatibility witness of the triple `(∅, u, ∅ ⟶ W)`: `V' = V` and `x' = u`. -/
theorem nonempty_compatibilityWitness_empty (V : BigFppfOver B S hS)
    (u : yoneda.obj V ⟶ c.U'.toFunctor) :
    Nonempty (CompatibilityWitness c V
      (Space.pointsMap B S hS (yoneda.obj V) (u ≫ c.U'.ι) ⁻¹' c.T')
      ((Space.openSubspaceOfPoints B S hS (yoneda.obj V)
        (Space.pointsMap B S hS (yoneda.obj V) (u ≫ c.U'.ι) ⁻¹' c.T')ᶜ).ι ≫ u)
      (Space.completionSheafMap B S hS (u ≫ c.U'.ι) c.T' ≫ c.g)) := by
  have hZ := c.preimage_T'_eq_empty u
  have hZ' : Space.pointsMap B S hS (yoneda.obj V) (𝟙 _) ⁻¹'
      (Space.pointsMap B S hS (yoneda.obj V) (u ≫ c.U'.ι) ⁻¹' c.T') = ∅ := by
    rw [Space.pointsMap_id, Set.preimage_id, hZ]
  have hsub : Space.pointsMap B S hS (yoneda.obj V) (𝟙 _) ⁻¹'
      (Space.pointsMap B S hS (yoneda.obj V) (u ≫ c.U'.ι) ⁻¹' c.T') ⊆
        Space.pointsMap B S hS (yoneda.obj V) (u ≫ c.U'.ι) ⁻¹' c.T' := by
    rw [hZ']
    exact Set.empty_subset _
  refine ⟨{ V' := yoneda.obj V
            isAlgebraicSpace_V' := isAlgebraicSpace_yoneda B S hS V
            p := 𝟙 _
            isProper_p := Space.isProper_of_isIso B S hS (𝟙 _)
            j := (Space.openSubspaceOfPoints B S hS (yoneda.obj V) _).ι
            isPullback_j := IsPullback.of_id_fst
            xhat' := Space.completionSheafRestrict B S hS (u ≫ c.U'.ι) _ c.T' hsub
            isPullback_xhat' := ?_
            x' := u ≫ c.U'.ι
            restrict_x' := (Category.assoc _ _ _).symm
            completion_x' := completionSheaf_yoneda_hom_ext_of_eq_empty hZ' _ _ }⟩
  refine IsPullback.of_map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    (completionSheaf_yoneda_hom_ext_of_eq_empty hZ' _ _) ?_
  refine IsPullback.of_forall_isPullback_app fun U => ?_
  refine (Types.isPullback_iff _ _ _ _).2 ⟨?_, fun a b _ => ?_, fun a b _ => ?_⟩
  · rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun φ => ((sheafToPresheaf (BigFppfOver.topology B S hS)
      (Type (u + 1))).map φ).app U) (completionSheaf_yoneda_hom_ext_of_eq_empty hZ' _ _)
  · exact (subsingleton_obj_of_completionSheaf_yoneda hZ' a _).elim _ _
  · have hU := bot_mem_of_completionSheaf_yoneda hZ a
    obtain ⟨e⟩ := Space.nonempty_of_bot_mem B S hS (Space.completionSheaf B S hS (yoneda.obj V)
      (Space.pointsMap B S hS (yoneda.obj V) (𝟙 _) ⁻¹'
        (Space.pointsMap B S hS (yoneda.obj V) (u ≫ c.U'.ι) ⁻¹' c.T'))).property hU
    refine ⟨e, ?_, ?_⟩ <;>
      exact (subsingleton_obj_of_completionSheaf_yoneda hZ a _).elim _ _

/-- The triple `(∅, u, ∅ ⟶ W)` of Artin's functor attached to `u : V ⟶ U'`. -/
noncomputable def emptyTriple (V : BigFppfOver B S hS) (u : yoneda.obj V ⟶ c.U'.toFunctor) :
    Triple c V where
  Z := Space.pointsMap B S hS (yoneda.obj V) (u ≫ c.U'.ι) ⁻¹' c.T'
  isClosed_Z := c.isClosed_T'.preimage (Space.continuous_pointsMap B S hS _)
  u := (Space.openSubspaceOfPoints B S hS (yoneda.obj V) _).ι ≫ u
  xhat := Space.completionSheafMap B S hS (u ≫ c.U'.ι) c.T' ≫ c.g
  adic_xhat := Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
    (Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS
      (isAlgebraicSpace_yoneda B S hS V) c.isAlgebraicSpace_X' (u ≫ c.U'.ι) c.T')
    c.isFormalModification_g.isProper.isRepresentable
  compatible := c.nonempty_compatibilityWitness_empty V u

/-- The closed subset of `(∅, u, ∅ ⟶ W)` is empty. -/
theorem emptyTriple_Z (V : BigFppfOver B S hS) (u : yoneda.obj V ⟶ c.U'.toFunctor) :
    (c.emptyTriple V u).Z = ∅ :=
  c.preimage_T'_eq_empty u

/-- The triple `(∅, u, ∅ ⟶ W)` is compatible with transport of triples. -/
theorem emptyTriple_comp {V₂ V₁ : BigFppfOver B S hS} (φ : V₂ ⟶ V₁)
    (u : yoneda.obj V₁ ⟶ c.U'.toFunctor) :
    c.emptyTriple V₂ (yoneda.map φ ≫ u) = mapTriple c φ (c.emptyTriple V₁ u) := by
  have hA : Space.pointsMap B S hS (yoneda.obj V₂) ((yoneda.map φ ≫ u) ≫ c.U'.ι) ⁻¹' c.T' =
      Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹'
        (Space.pointsMap B S hS (yoneda.obj V₁) (u ≫ c.U'.ι) ⁻¹' c.T') := by
    rw [Category.assoc, Space.pointsMap_comp, Set.preimage_comp]
  refine Triple.mk_congr hA ?_ ?_
  · have key : ∀ (A : Set (Space.points B S hS (yoneda.obj V₂)))
        (_ : A = Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹'
          (Space.pointsMap B S hS (yoneda.obj V₁) (u ≫ c.U'.ι) ⁻¹' c.T')),
        HEq ((Space.openSubspaceOfPoints B S hS (yoneda.obj V₂) Aᶜ).ι ≫ yoneda.map φ ≫ u)
          (Space.openSubspaceOfPointsRestrict B S hS (yoneda.map φ)
            (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹'
              (Space.pointsMap B S hS (yoneda.obj V₁) (u ≫ c.U'.ι) ⁻¹' c.T'))ᶜ
            (Space.pointsMap B S hS (yoneda.obj V₁) (u ≫ c.U'.ι) ⁻¹' c.T')ᶜ (fun _ hz => hz) ≫
              (Space.openSubspaceOfPoints B S hS (yoneda.obj V₁)
                (Space.pointsMap B S hS (yoneda.obj V₁) (u ≫ c.U'.ι) ⁻¹' c.T')ᶜ).ι ≫ u) := by
      rintro A rfl
      refine heq_of_eq ?_
      have k1 := Space.openSubspaceOfPointsRestrict_comp_ι B S hS (yoneda.map φ)
        (Space.pointsMap B S hS (yoneda.obj V₂) (yoneda.map φ) ⁻¹'
          (Space.pointsMap B S hS (yoneda.obj V₁) (u ≫ c.U'.ι) ⁻¹' c.T'))ᶜ
        (Space.pointsMap B S hS (yoneda.obj V₁) (u ≫ c.U'.ι) ⁻¹' c.T')ᶜ (fun _ hz => hz)
      rw [← Category.assoc, ← k1, Category.assoc]
    exact key _ hA
  · exact heq_completionSheafRestrict_comp (yoneda.map φ) (u ≫ c.U'.ι)
      (k := (yoneda.map φ ≫ u) ≫ c.U'.ι) (by rw [Category.assoc]) hA (fun _ h => h)
      (fun _ h => h) (fun _ h => h) c.g

variable (α : contractionFunctor c ≅ morOnLocallyNoetherian B S hS X)

/-- The section of `X ∖ T` matched by `α` with the triple `(∅, u, ∅ ⟶ W)`. -/
noncomputable def openPartSection (V : LocallyNoetherianOver B S hS)
    (u : yoneda.obj V.obj ⟶ c.U'.toFunctor) :
    (Space.openSubspaceOfPoints B S hS X (contractedLocus c α)ᶜ).toFunctor.obj (op V.obj) :=
  ⟨(α.hom.app (op V) (c.emptyTriple V.obj u)).down, by
    rw [Space.mem_openSubspaceOfPoints_iff]
    rintro _ ⟨z, rfl⟩ hz
    have h := preimage_contractedLocus c α V
      (yonedaEquiv.symm (α.hom.app (op V) (c.emptyTriple V.obj u)).down)
    rw [tripleOfMor_yonedaEquiv_symm_hom_app, emptyTriple_Z] at h
    exact h.subset hz⟩

/-- An open subspace of an algebraic space locally of finite type over `S` is locally of finite
type over `S`: its inclusion is étale. -/
theorem isLocallyOfFiniteType_terminal_of_isOpenSubspace {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from F))
    {V : Subfunctor F} (hV : Space.IsOpenSubspace B S hS V) :
    Space.IsLocallyOfFiniteType B S hS (terminal.from V.toFunctor) := by
  let e : yoneda.obj (Over.mk (𝟙 (B.obj hS))) ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B S hS e.symm (isAlgebraicSpace_yoneda B S hS _)
  rw [show terminal.from V.toFunctor = V.ι ≫ terminal.from F from terminal.hom_ext _ _]
  exact Space.isLocallyOfFiniteType_comp' (f := V.ι) (g := terminal.from F) (hG := hF) (hH := hT)
    (hf := Space.isLocallyOfFiniteType_of_isEtale' B S hS V.ι
      (Space.isEtale_ι_of_isOpenSubspace hV)) (hg := hft)

/-- The sections `(∅, u, ∅ ⟶ W) ↦ α(∅, u, ∅ ⟶ W)` of `X ∖ T`, as a transformation of functors on
locally Noetherian schemes over `S` from `U'` to `X ∖ T`. -/
noncomputable def openPartTrans :
    (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙ c.U'.toFunctor ⋙
          uliftFunctor.{u + 1} ⟶
      (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op ⋙
        (Space.openSubspaceOfPoints B S hS X (contractedLocus c α)ᶜ).toFunctor ⋙
          uliftFunctor.{u + 1} where
  app V := ↾fun a => ULift.up (openPartSection c α V.unop (yonedaEquiv.symm a.down))
  naturality V₁ V₂ φ := by
    ext a
    apply ULift.ext
    apply Subtype.ext
    change (α.hom.app (op V₂.unop) (c.emptyTriple V₂.unop.obj
      (yonedaEquiv.symm (c.U'.toFunctor.map φ.unop.hom.op a.down)))).down =
      X.map φ.unop.hom.op (α.hom.app (op V₁.unop) (c.emptyTriple V₁.unop.obj
        (yonedaEquiv.symm a.down))).down
    have h1 : yonedaEquiv.symm (c.U'.toFunctor.map φ.unop.hom.op a.down) =
        yoneda.map φ.unop.hom ≫ yonedaEquiv.symm a.down := by
      apply yonedaEquiv.injective
      rw [Equiv.apply_symm_apply, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
      exact (yonedaEquiv_symm_app_apply (X := V₁.unop.obj) a.down (op V₂.unop.obj)
        φ.unop.hom).symm
    rw [h1, emptyTriple_comp]
    exact congrArg ULift.down (NatTrans.naturality_apply α.hom φ
      (c.emptyTriple V₁.unop.obj (yonedaEquiv.symm a.down)))

/-- The inclusion of the open subspace cut out by all points is an epimorphism. -/
theorem epi_ι_openSubspaceOfPoints_of_eq_univ {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (W : Set (Space.points B S hS F)) (hW : W = Set.univ) :
    Epi (Space.openSubspaceOfPoints B S hS F W).ι := by
  subst hW
  have : IsIso (Space.openSubspaceOfPoints B S hS F Set.univ).ι :=
    (Subfunctor.eq_top_iff_isIso _).mp (Space.openSubspaceOfPoints_univ B S hS (F := F))
  exact IsIso.epi_of_iso _

/-- A triple whose closed subset is empty is the triple `(∅, u, ∅ ⟶ W)` of its second
component. -/
theorem Triple.eq_emptyTriple {V : BigFppfOver B S hS} (t : Triple c V)
    (u : yoneda.obj V ⟶ c.U'.toFunctor) (hZ : t.Z = ∅)
    (hu : (Space.openSubspaceOfPoints B S hS (yoneda.obj V) t.Zᶜ).ι ≫ u = t.u) :
    t = c.emptyTriple V u := by
  obtain ⟨Z, hc, tu, tx, ta, tw⟩ := t
  simp only at hZ hu
  subst hZ
  have hZe := c.emptyTriple_Z V u
  refine Triple.mk_congr hZe.symm ?_ ?_
  · have key : ∀ (A : Set (Space.points B S hS (yoneda.obj V))) (_ : ∅ = A),
        HEq ((Space.openSubspaceOfPoints B S hS (yoneda.obj V) (∅ : Set _)ᶜ).ι ≫ u)
          ((Space.openSubspaceOfPoints B S hS (yoneda.obj V) Aᶜ).ι ≫ u) := by
      rintro A rfl
      rfl
    exact (heq_of_eq hu.symm).trans (key _ hZe.symm)
  · have key : ∀ (A : Set (Space.points B S hS (yoneda.obj V))) (_ : ∅ = A)
        (x : Space.completionSheaf B S hS (yoneda.obj V) ∅ ⟶ c.W)
        (y : Space.completionSheaf B S hS (yoneda.obj V) A ⟶ c.W), HEq x y := by
      rintro A rfl x y
      exact heq_of_eq (completionSheaf_yoneda_hom_ext_of_eq_empty rfl x y)
    exact key _ hZe.symm _ _

include c in
/-- Morphisms between algebraic spaces locally of finite type over the locally Noetherian `S`
are determined on locally Noetherian schemes. -/
theorem hom_ext_of_locallyNoetherian {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hFft : Space.IsLocallyOfFiniteType B S hS (terminal.from F))
    (hG : IsAlgebraicSpace B S hS G) (hGft : Space.IsLocallyOfFiniteType B S hS (terminal.from G))
    {f g : F ⟶ G} (h : ∀ (V : LocallyNoetherianOver B S hS) (x : yoneda.obj V.obj ⟶ F),
      x ≫ f = x ≫ g) : f = g := by
  have := c.isLocallyNoetherian_base
  obtain ⟨_, _, hu⟩ := Space.existsUnique_hom_whiskerRight_whiskerLeft_eq B S hS hF hFft hG hGft
    (Functor.whiskerRight (Functor.whiskerLeft
      (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
        IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op f) uliftFunctor.{u + 1})
  refine (hu f rfl).trans (hu g ?_).symm
  ext V a
  apply ULift.ext
  have h' := congrArg yonedaEquiv (h V.unop (yonedaEquiv.symm a.down))
  rw [yonedaEquiv_comp, yonedaEquiv_comp, Equiv.apply_symm_apply] at h'
  exact h'.symm

variable {hX : IsAlgebraicSpace B S hS X}
    {hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)}

include hft in
/-- `X ∖ T` is an open subspace of `X`. -/
theorem isOpenSubspace_openPart (hX : IsAlgebraicSpace B S hS X) :
    Space.IsOpenSubspace B S hS (Space.openSubspaceOfPoints B S hS X (contractedLocus c α)ᶜ) :=
  Space.isOpenSubspace_openSubspaceOfPoints B S hS hX _
    (isClosed_contractedLocus c α hX hft).isOpen_compl

/-- The morphism `U' ⟶ X ∖ T` extending `u ↦ α(∅, u, ∅ ⟶ W)` (Stacks 0GE3). -/
theorem existsUnique_openPartHom (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    ∃! f : c.U'.toFunctor ⟶ (Space.openSubspaceOfPoints B S hS X (contractedLocus c α)ᶜ).toFunctor,
      Functor.whiskerRight (Functor.whiskerLeft
        (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
          IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))).op f)
          uliftFunctor.{u + 1} = openPartTrans c α := by
  have := c.isLocallyNoetherian_base
  exact Space.existsUnique_hom_whiskerRight_whiskerLeft_eq B S hS c.isOpenSubspace_U'.1
    (isLocallyOfFiniteType_terminal_of_isOpenSubspace c.isAlgebraicSpace_X'
      c.isLocallyOfFiniteType_X' c.isOpenSubspace_U')
    (isOpenSubspace_openPart c α (hft := hft) hX).1
    (isLocallyOfFiniteType_terminal_of_isOpenSubspace hX hft
      (isOpenSubspace_openPart c α (hft := hft) hX)) _

/-- The morphism `U' ⟶ X ∖ T`. -/
noncomputable def openPartHom (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X)) :
    c.U'.toFunctor ⟶ (Space.openSubspaceOfPoints B S hS X (contractedLocus c α)ᶜ).toFunctor :=
  (existsUnique_openPartHom c α hX hft).exists.choose

/-- For a locally Noetherian `V` and `u : V ⟶ U'`, the composite of `u` with `openPartHom` and
the inclusion `X ∖ T ⟶ X` is the point `α(∅, u, ∅ ⟶ W)` of `X`. -/
theorem comp_openPartHom_ι (hX : IsAlgebraicSpace B S hS X)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from X))
    (V : LocallyNoetherianOver B S hS) (u : yoneda.obj V.obj ⟶ c.U'.toFunctor) :
    u ≫ openPartHom c α hX hft ≫
        (Space.openSubspaceOfPoints B S hS X (contractedLocus c α)ᶜ).ι =
      yonedaEquiv.symm (α.hom.app (op V) (c.emptyTriple V.obj u)).down := by
  have h := congrArg (fun τ => (τ.app (op V) (ULift.up (yonedaEquiv (C := BigFppfOver B S hS)
    (X := V.obj) u))).down) (existsUnique_openPartHom c α hX hft).exists.choose_spec
  rw [Equiv.eq_symm_apply, yonedaEquiv_comp]
  show ((openPartHom c α hX hft).app (op V.obj) (yonedaEquiv u)).1 = _
  refine (congrArg Subtype.val h).trans ?_
  show (α.hom.app (op V) (c.emptyTriple V.obj (yonedaEquiv.symm (yonedaEquiv u)))).down = _
  rw [Equiv.symm_apply_apply]

end AlgebraicGeometry.Artin.ContractionSituation

end
