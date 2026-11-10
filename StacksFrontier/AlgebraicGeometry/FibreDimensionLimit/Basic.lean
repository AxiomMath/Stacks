module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Filtered.FinallySmall
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.NoetherianSpace
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimension

/-!
# Fibre dimension in a cofiltered inverse limit of schemes

Let `(f_i : X_i ⟶ S_i)` be an inverse system of morphisms of schemes over a cofiltered index
category, with the transition morphisms of the bases affine, the bases quasi-compact, the `f_i`
of finite type, and the canonical morphisms `X_i ⟶ X_j ×_{S_j} S_i` closed immersions. Let
`f : X = lim X_i ⟶ S = lim S_i` be the limit. If every fibre of `f` has dimension at most `d`
then so does every fibre of some `f_i`. This is [Stacks, Tag 05M5].

## Main definitions

* `AlgebraicGeometry.baseChangeSystem` is the inverse system of base changes `T ×_{S_i} X_i` of
  the stages along a morphism `g : T ⟶ lim S_i`, and `AlgebraicGeometry.baseChangeSystemCone` is
  the cone over it with vertex `T ×_{lim S_i} lim X_i`.

## Main results

* `AlgebraicGeometry.isLimitBaseChangeSystemCone`: base change commutes with a cofiltered limit
  of morphisms of schemes. The base change of the limit morphism along any `g : T ⟶ lim S_i` is
  the limit of the base changes of the stages.
* `AlgebraicGeometry.isClosedImmersion_baseChangeSystem_map`: the transition morphisms of that
  system are closed immersions as soon as the morphisms `X_i ⟶ X_j ×_{S_j} S_i` are.
* `AlgebraicGeometry.mem_range_π_app_of_isClosed_singleton`: a closed point of a stage of a
  cofiltered system with affine transitions which lifts to every earlier stage lifts to the limit.
* `AlgebraicGeometry.exists_topologicalKrullDim_eq_of_isLimit`: for a cofiltered system whose
  transition morphisms and limit projections are closed immersions and one of whose stages is
  Noetherian and Jacobson, the dimension of the limit is attained at some stage.
* `AlgebraicGeometry.topologicalKrullDim_fiber_le_iff`: a fibre has dimension at most `d` exactly
  when the local dimension of the fibre at each of its points is at most `d`.
* `AlgebraicGeometry.exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_cofiltered`: the
  dimension bound on the fibres of the limit morphism holds at some finite stage, for an index
  category in the universe of the schemes.
* `AlgebraicGeometry.exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_initiallySmall` and
  `AlgebraicGeometry.exists_forall_topologicalKrullDim_fiber_le_of_isLimit`: the same with the
  index universes independent of the universe of the schemes, the second in the shape of
  [Stacks, Tag 05M5] itself. Both carry the hypothesis that the canonical morphisms
  `lim X_i ⟶ X_i ×_{S_i} lim S_j` are closed immersions.

## References

* [Stacks Project, Tag 05M5](https://stacks.math.columbia.edu/tag/05M5)
* [Stacks Project, Tag 02FY](https://stacks.math.columbia.edu/tag/02FY)
* [Stacks Project, Tag 02FZ](https://stacks.math.columbia.edu/tag/02FZ)
* [Stacks Project, Tag 01Z3](https://stacks.math.columbia.edu/tag/01Z3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.InitiallySmall AlgebraicGeometry
  TopologicalSpace

universe u uI v

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

namespace AlgebraicGeometry

/-! ### Base change commutes with a cofiltered limit -/

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {X S : I ⥤ Scheme.{u}} (φ : X ⟶ S)
  {cX : Cone X} (hcX : IsLimit cX) {cS : Cone S} (hcS : IsLimit cS)
  {f : cX.pt ⟶ cS.pt} (hf : ∀ i, cX.π.app i ≫ φ.app i = f ≫ cS.π.app i)
  {T : Scheme.{u}} (g : T ⟶ cS.pt)

/-- The diagram of base changes of the stages of a morphism of systems along a morphism `g` to
the limit of the bases. -/
@[simps, reducible]
noncomputable def baseChangeSystem : I ⥤ Scheme.{u} where
  obj i := pullback (φ.app i) (g ≫ cS.π.app i)
  map {i j} h := pullback.map _ _ _ _ (X.map h) (𝟙 T) (S.map h) (φ.naturality h).symm (by
    simp [cS.w h])
  map_id i := by
    refine pullback.hom_ext ?_ ?_ <;> simp [pullback.map]
  map_comp {i j k} h₁ h₂ := by
    refine pullback.hom_ext ?_ ?_ <;>
      simp [pullback.map]

omit [IsCofiltered I] in
/-- A transition morphism of `AlgebraicGeometry.baseChangeSystem` followed by the first
projection is the first projection followed by the transition morphism of `X`. -/
@[simp] lemma baseChangeDiagram_map_fst {i j : I} (h : i ⟶ j) :
    (baseChangeSystem φ g).map h ≫ pullback.fst (φ.app j) (g ≫ cS.π.app j) =
      pullback.fst (φ.app i) (g ≫ cS.π.app i) ≫ X.map h :=
  pullback.lift_fst _ _ _

omit [IsCofiltered I] in
/-- A transition morphism of `AlgebraicGeometry.baseChangeSystem` commutes with the second
projections to `T`. -/
@[simp] lemma baseChangeDiagram_map_snd {i j : I} (h : i ⟶ j) :
    (baseChangeSystem φ g).map h ≫ pullback.snd (φ.app j) (g ≫ cS.π.app j) =
      pullback.snd (φ.app i) (g ≫ cS.π.app i) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The cone over `AlgebraicGeometry.baseChangeSystem` whose vertex is the base change of the
limit morphism along `g`. -/
@[simps, reducible]
noncomputable def baseChangeSystemCone : Cone (baseChangeSystem φ g) where
  pt := pullback f g
  π :=
    { app i := pullback.map _ _ _ _ (cX.π.app i) (𝟙 T) (cS.π.app i) (hf i).symm (by simp)
      naturality := fun i j h ↦ by
        refine pullback.hom_ext ?_ ?_ <;>
          simp [baseChangeSystem, pullback.map, cX.w h] }

omit [IsCofiltered I] in
/-- A projection of `AlgebraicGeometry.baseChangeSystemCone` followed by the first projection is
the first projection followed by the projection of `cX`. -/
@[simp] lemma baseChangeCone_π_fst (i : I) :
    (baseChangeSystemCone φ hf g).π.app i ≫ pullback.fst (φ.app i) (g ≫ cS.π.app i) =
      pullback.fst f g ≫ cX.π.app i :=
  pullback.lift_fst _ _ _

omit [IsCofiltered I] in
/-- A projection of `AlgebraicGeometry.baseChangeSystemCone` commutes with the second projections
to `T`. -/
@[simp] lemma baseChangeCone_π_snd (i : I) :
    (baseChangeSystemCone φ hf g).π.app i ≫ pullback.snd (φ.app i) (g ≫ cS.π.app i) =
      pullback.snd f g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The `T`-component of a cone over `AlgebraicGeometry.baseChangeSystem` does not depend on the
index. -/
lemma baseChangeDiagram_cone_snd_eq (s : Cone (baseChangeSystem φ g)) (i j : I) :
    s.π.app i ≫ pullback.snd (φ.app i) (g ≫ cS.π.app i) =
      s.π.app j ≫ pullback.snd (φ.app j) (g ≫ cS.π.app j) := by
  have key : ∀ (a b : I) (h : a ⟶ b),
      s.π.app a ≫ pullback.snd (φ.app a) (g ≫ cS.π.app a) =
        s.π.app b ≫ pullback.snd (φ.app b) (g ≫ cS.π.app b) := by
    intro a b h
    calc s.π.app a ≫ pullback.snd (φ.app a) (g ≫ cS.π.app a)
        = s.π.app a ≫ ((baseChangeSystem φ g).map h ≫
            pullback.snd (φ.app b) (g ≫ cS.π.app b)) := by rw [baseChangeDiagram_map_snd]
      _ = (s.π.app a ≫ (baseChangeSystem φ g).map h) ≫
            pullback.snd (φ.app b) (g ≫ cS.π.app b) := (Category.assoc _ _ _).symm
      _ = s.π.app b ≫ pullback.snd (φ.app b) (g ≫ cS.π.app b) := by rw [s.w h]
  rw [← key _ _ (IsCofiltered.minToLeft i j), ← key _ _ (IsCofiltered.minToRight i j)]

/-- The cone over `X` obtained from a cone over `AlgebraicGeometry.baseChangeSystem`. -/
@[reducible]
noncomputable def baseChangeSystem.coneX (s : Cone (baseChangeSystem φ g)) : Cone X where
  pt := s.pt
  π :=
    { app i := s.π.app i ≫ pullback.fst (φ.app i) (g ≫ cS.π.app i)
      naturality := fun i j h ↦ by
        have key : s.π.app j ≫ pullback.fst (φ.app j) (g ≫ cS.π.app j) =
            (s.π.app i ≫ pullback.fst (φ.app i) (g ≫ cS.π.app i)) ≫ X.map h :=
          calc s.π.app j ≫ pullback.fst (φ.app j) (g ≫ cS.π.app j)
              = (s.π.app i ≫ (baseChangeSystem φ g).map h) ≫
                  pullback.fst (φ.app j) (g ≫ cS.π.app j) := by rw [s.w h]
            _ = s.π.app i ≫ ((baseChangeSystem φ g).map h ≫
                  pullback.fst (φ.app j) (g ≫ cS.π.app j)) := Category.assoc _ _ _
            _ = s.π.app i ≫ (pullback.fst (φ.app i) (g ≫ cS.π.app i) ≫ X.map h) := by
                  rw [baseChangeDiagram_map_fst]
            _ = (s.π.app i ≫ pullback.fst (φ.app i) (g ≫ cS.π.app i)) ≫ X.map h :=
                  (Category.assoc _ _ _).symm
        simpa using key }

omit [IsCofiltered I] in
/-- The projections of `AlgebraicGeometry.baseChangeSystem.coneX s` are those of `s` followed by
the first projections. -/
@[simp] lemma baseChangeSystem.coneX_π (s : Cone (baseChangeSystem φ g)) (i : I) :
    (baseChangeSystem.coneX φ g s).π.app i =
      s.π.app i ≫ pullback.fst (φ.app i) (g ≫ cS.π.app i) := rfl

variable (i₀ : I)

include hcS hf in
/-- The two morphisms out of the vertex of a cone over `AlgebraicGeometry.baseChangeSystem`, to
`lim X` and to `T`, agree in `lim S`. -/
lemma baseChangeSystem.lift_aux (s : Cone (baseChangeSystem φ g)) :
    hcX.lift (baseChangeSystem.coneX φ g s) ≫ f =
      (s.π.app i₀ ≫ pullback.snd (φ.app i₀) (g ≫ cS.π.app i₀)) ≫ g := by
  refine hcS.hom_ext fun i ↦ ?_
  have h1 : hcX.lift (baseChangeSystem.coneX φ g s) ≫ cX.π.app i =
      s.π.app i ≫ pullback.fst (φ.app i) (g ≫ cS.π.app i) :=
    hcX.fac (baseChangeSystem.coneX φ g s) i
  have h2 := baseChangeDiagram_cone_snd_eq φ g s i₀ i
  have h3 : pullback.fst (φ.app i) (g ≫ cS.π.app i) ≫ φ.app i =
      pullback.snd (φ.app i) (g ≫ cS.π.app i) ≫ (g ≫ cS.π.app i) := pullback.condition
  rw [Category.assoc, ← hf i, ← Category.assoc, h1, Category.assoc, h3, ← Category.assoc, h2]
  simp

/-- The morphism into `T ×_{lim S} lim X` induced by a cone over
`AlgebraicGeometry.baseChangeSystem`. -/
noncomputable def baseChangeSystem.lift (s : Cone (baseChangeSystem φ g)) :
    s.pt ⟶ pullback f g :=
  pullback.lift (hcX.lift (baseChangeSystem.coneX φ g s))
    (s.π.app i₀ ≫ pullback.snd (φ.app i₀) (g ≫ cS.π.app i₀))
    (baseChangeSystem.lift_aux φ hcX hcS hf g i₀ s)

/-- The first component of `AlgebraicGeometry.baseChangeSystem.lift`. -/
@[reassoc (attr := simp)]
lemma baseChangeSystem.lift_fst (s : Cone (baseChangeSystem φ g)) :
    baseChangeSystem.lift φ hcX hcS hf g i₀ s ≫ pullback.fst f g =
      hcX.lift (baseChangeSystem.coneX φ g s) :=
  pullback.lift_fst _ _ _

/-- The second component of `AlgebraicGeometry.baseChangeSystem.lift`. -/
@[reassoc (attr := simp)]
lemma baseChangeSystem.lift_snd (s : Cone (baseChangeSystem φ g)) :
    baseChangeSystem.lift φ hcX hcS hf g i₀ s ≫ pullback.snd f g =
      s.π.app i₀ ≫ pullback.snd (φ.app i₀) (g ≫ cS.π.app i₀) :=
  pullback.lift_snd _ _ _

/-- Auxiliary form of `AlgebraicGeometry.isLimitBaseChangeSystemCone` with the index at which the
`T`-component of a cone is read off supplied explicitly. -/
noncomputable def isLimitBaseChangeSystemConeAux : IsLimit (baseChangeSystemCone φ hf g) :=
  IsLimit.mk (fun s ↦ baseChangeSystem.lift φ hcX hcS hf g i₀ s)
    (fun s i ↦ by
      refine pullback.hom_ext ?_ ?_
      · dsimp only [baseChangeSystemCone_π_app]
        simp [pullback.map, hcX.fac (baseChangeSystem.coneX φ g s) i]
      · dsimp only [baseChangeSystemCone_π_app]
        simp [pullback.map,
          baseChangeDiagram_cone_snd_eq φ g s i₀ i])
    (fun s m hm ↦ by
      refine pullback.hom_ext (hcX.hom_ext fun i ↦ ?_) ?_
      · have h1 : (m ≫ pullback.fst f g) ≫ cX.π.app i =
            (m ≫ (baseChangeSystemCone φ hf g).π.app i) ≫
              pullback.fst (φ.app i) (g ≫ cS.π.app i) := by simp
        rw [h1, hm i]
        simp [hcX.fac (baseChangeSystem.coneX φ g s) i]
      · have h2 : m ≫ pullback.snd f g =
            (m ≫ (baseChangeSystemCone φ hf g).π.app i₀) ≫
              pullback.snd (φ.app i₀) (g ≫ cS.π.app i₀) := by simp
        rw [h2, hm i₀]
        simp)

/-- Base change commutes with a cofiltered limit of morphisms of schemes: if `X` and `S` are
cofiltered inverse systems of schemes, `φ : X ⟶ S` a morphism of systems, `f` the induced
morphism between the limits and `g : T ⟶ lim S` any morphism, then `T ×_{lim S} lim X` is the
limit of the system of base changes `T ×_{S i} X i`. -/
noncomputable def isLimitBaseChangeSystemCone : IsLimit (baseChangeSystemCone φ hf g) :=
  isLimitBaseChangeSystemConeAux φ hcX hcS hf g (Nonempty.some IsCofiltered.nonempty)


/-! ### The transition morphisms of the base-changed system -/

/-- The square exhibiting the base change along `τi` of the canonical morphism
`Xi ⟶ Xj ×_{Sj} Si` as the morphism `Xi ×_{Si} T ⟶ Xj ×_{Sj} T`. -/
lemma isPullback_pullback_map_id {Xi Xj Si Sj T : Scheme.{u}} (fi : Xi ⟶ Si) (fj : Xj ⟶ Sj)
    (u : Xi ⟶ Xj) (σ : Si ⟶ Sj) (hc : fi ≫ σ = u ≫ fj) (τi : T ⟶ Si) (τj : T ⟶ Sj)
    (hτ : τi ≫ σ = τj) :
    IsPullback (pullback.map fi τi fj τj u (𝟙 T) σ hc (by rw [Category.id_comp, hτ]))
      (pullback.fst fi τi)
      (pullback.lift (pullback.fst fj τj) (pullback.snd fj τj ≫ τi)
        (by rw [pullback.condition, Category.assoc, hτ]))
      (pullback.lift u fi hc.symm) := by
  have ht : IsPullback (pullback.snd fj τj)
      (pullback.lift (pullback.fst fj τj) (pullback.snd fj τj ≫ τi)
        (by rw [pullback.condition, Category.assoc, hτ])) τi (pullback.snd fj σ) := by
    refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback fj σ).flip
    · have h1 : pullback.lift (pullback.fst fj τj) (pullback.snd fj τj ≫ τi)
          (by rw [pullback.condition, Category.assoc, hτ]) ≫ pullback.fst fj σ =
          pullback.fst fj τj := pullback.lift_fst _ _ _
      have h2 : τi ≫ σ = τj := hτ
      rw [h1, h2]
      exact (IsPullback.of_hasPullback fj τj).flip
    · exact (pullback.lift_snd _ _ _).symm
  have h1 : pullback.map fi τi fj τj u (𝟙 T) σ hc (by rw [Category.id_comp, hτ]) ≫
      pullback.snd fj τj = pullback.snd fi τi :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine IsPullback.of_right ?_ ?_ ht
  · have h2 : pullback.lift u fi hc.symm ≫ pullback.snd fj σ = fi := pullback.lift_snd _ _ _
    rw [h1, h2]
    exact (IsPullback.of_hasPullback fi τi).flip
  · refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, h1]
      exact pullback.condition.symm

omit [IsCofiltered I] in
/-- The transition morphisms of the base-changed system are closed immersions as soon as the
canonical morphisms `X i ⟶ X j ×_{S j} S i` are. -/
lemma isClosedImmersion_baseChangeSystem_map {i j : I} (h : i ⟶ j)
    [IsClosedImmersion (pullback.lift (X.map h) (φ.app i) (φ.naturality h))] :
    IsClosedImmersion ((baseChangeSystem φ g).map h) :=
  MorphismProperty.of_isPullback
    (isPullback_pullback_map_id (φ.app i) (φ.app j) (X.map h) (S.map h) (φ.naturality h).symm
      (g ≫ cS.π.app i) (g ≫ cS.π.app j) (by rw [Category.assoc, cS.w h])).flip
    inferInstance

/-- The underlying space of a closed immersion has the same dimension as its range. -/
private lemma topologicalKrullDim_eq_range {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    topologicalKrullDim X = topologicalKrullDim (Set.range f) :=
  IsHomeomorph.topologicalKrullDim_eq _
    ((IsClosedImmersion.isClosedEmbedding f).isEmbedding.toHomeomorph).isHomeomorph

section ClosedImmersionLimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)] [∀ i, CompactSpace (D.obj i)]
  (c : Cone D) (hc : IsLimit c)

include hc in
/-- A closed point of a stage of a cofiltered inverse system of schemes with affine transition
morphisms which lifts to every earlier stage lifts to the limit. -/
lemma mem_range_π_app_of_isClosed_singleton {i₀ : I} (y : D.obj i₀) (hy : IsClosed {y})
    (hmem : ∀ (j : I) (h : j ⟶ i₀), y ∈ Set.range (D.map h)) :
    y ∈ Set.range (c.π.app i₀) := by
  obtain ⟨p, hp⟩ := exists_mem_of_isClosed_of_nonempty' D c hc (j := i₀)
    (fun j h ↦ (D.map h) ⁻¹' {y})
    (fun j h ↦ hy.preimage (D.map h).continuous)
    (fun j h ↦ hmem j h)
    (fun j h ↦ (hy.preimage (D.map h).continuous).isCompact)
    (fun j j' hj'j hj x hx ↦ by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
      rwa [← Scheme.Hom.comp_apply, ← D.map_comp])
  exact ⟨p, by simpa using hp i₀ (𝟙 i₀)⟩

omit [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)] [∀ i, CompactSpace (D.obj i)] in
/-- In a cofiltered inverse system of schemes whose transition morphisms are closed immersions,
the images in a fixed stage with Noetherian underlying space have a smallest member. -/
lemma exists_min_range_map [∀ {i j : I} (h : i ⟶ j), IsClosedImmersion (D.map h)] (i₀ : I)
    [NoetherianSpace (D.obj i₀)] :
    ∃ (j₁ : I) (h₁ : j₁ ⟶ i₀), ∀ (j : I) (h : j ⟶ i₀),
      Set.range (D.map h₁) ⊆ Set.range (D.map h) := by
  classical
  have hcl : ∀ (j : I) (h : j ⟶ i₀), IsClosed (Set.range (D.map h)) := fun j h ↦
    (IsClosedImmersion.isClosedEmbedding (D.map h)).isClosed_range
  set F : (Σ j : I, j ⟶ i₀) → Closeds (D.obj i₀) := fun p ↦ ⟨Set.range (D.map p.2), hcl p.1 p.2⟩
    with hF
  obtain ⟨a, ⟨p₁, hp₁⟩, hmin⟩ :=
    (wellFounded_lt (α := Closeds (D.obj i₀))).has_min
      (Set.range F) ⟨F ⟨i₀, 𝟙 i₀⟩, ⟨i₀, 𝟙 i₀⟩, rfl⟩
  refine ⟨p₁.1, p₁.2, fun j h ↦ ?_⟩
  obtain ⟨k, u, v, -⟩ := IsCofilteredOrEmpty.cone_objs p₁.1 j
  obtain ⟨k', w, hw⟩ := IsCofilteredOrEmpty.cone_maps (u ≫ p₁.2) (v ≫ h)
  have hle₁ : F ⟨k', w ≫ u ≫ p₁.2⟩ ≤ F ⟨p₁.1, p₁.2⟩ := by
    intro z hz
    obtain ⟨x, rfl⟩ := hz
    exact ⟨D.map (w ≫ u) x, by rw [← Scheme.Hom.comp_apply, ← D.map_comp, Category.assoc]⟩
  have hle₂ : F ⟨k', w ≫ u ≫ p₁.2⟩ ≤ a := hp₁ ▸ hle₁
  have heq : F ⟨k', w ≫ u ≫ p₁.2⟩ = a := by
    rcases eq_or_lt_of_le hle₂ with h' | h'
    · exact h'
    · exact absurd h' (hmin _ ⟨⟨k', w ≫ u ≫ p₁.2⟩, rfl⟩)
  intro z hz
  have hz' : z ∈ F ⟨k', w ≫ u ≫ p₁.2⟩ := by rwa [heq, ← hp₁]
  obtain ⟨x, rfl⟩ := hz'
  exact ⟨D.map (w ≫ v) x, by
    rw [← Scheme.Hom.comp_apply, ← D.map_comp,
      show (w ≫ v) ≫ h = w ≫ u ≫ p₁.2 from by
        simp only [Category.assoc]; exact hw.symm]⟩

include hc in
/-- In a cofiltered inverse system of schemes whose transition
morphisms are closed immersions, with one stage Noetherian and Jacobson and all the projections
from the limit closed immersions, the dimension of the limit is attained at some stage. -/
lemma exists_topologicalKrullDim_eq_of_isLimit
    [∀ {i j : I} (h : i ⟶ j), IsClosedImmersion (D.map h)] (i₀ : I)
    [NoetherianSpace (D.obj i₀)] [JacobsonSpace (D.obj i₀)]
    (hπ : ∀ j : I, IsClosedImmersion (c.π.app j)) :
    ∃ j : I, topologicalKrullDim (D.obj j) = topologicalKrullDim c.pt := by
  obtain ⟨j₁, h₁, hmin⟩ := exists_min_range_map D i₀
  have hcl₁ : IsClosed (Set.range (D.map h₁)) :=
    (IsClosedImmersion.isClosedEmbedding (D.map h₁)).isClosed_range
  have := hπ i₀
  have hclR : IsClosed (Set.range (c.π.app i₀)) :=
    (IsClosedImmersion.isClosedEmbedding (c.π.app i₀)).isClosed_range
  have hR : Set.range (c.π.app i₀) = Set.range (D.map h₁) := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro z ⟨p, rfl⟩
      exact ⟨c.π.app j₁ p, by rw [← Scheme.Hom.comp_apply, c.w h₁]⟩
    · have hsub : Set.range (D.map h₁) ∩ closedPoints (D.obj i₀) ⊆
          Set.range (c.π.app i₀) := by
        rintro y ⟨hy1, hy2⟩
        exact mem_range_π_app_of_isClosed_singleton D c hc y hy2 (fun j h ↦ hmin j h hy1)
      calc Set.range (D.map h₁)
          = closure (Set.range (D.map h₁) ∩ closedPoints (D.obj i₀)) := by
            rw [JacobsonSpace.closure_inter_closedPoints_eq_closure hcl₁.isLocallyClosed,
              hcl₁.closure_eq]
        _ ⊆ closure (Set.range (c.π.app i₀)) := closure_mono hsub
        _ = Set.range (c.π.app i₀) := hclR.closure_eq
  refine ⟨j₁, ?_⟩
  rw [topologicalKrullDim_eq_range (D.map h₁), ← hR]
  exact (topologicalKrullDim_eq_range (c.π.app i₀)).symm

end ClosedImmersionLimit

/-! ### Fibre dimension, globally and pointwise -/

/-- The dimension of a fibre is at most `d` exactly when the local dimension of the fibre through
every point of that fibre is at most `d`. -/
theorem topologicalKrullDim_fiber_le_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y)
    (d : WithBot ℕ∞) :
    topologicalKrullDim (f.fiber s) ≤ d ↔
      ∀ x : X, f x = s →
        topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ d := by
  have key : ∀ (x : X) (hx : f x = s),
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
        topologicalKrullDimAt ((f : X → Y) ⁻¹' {s}) ⟨x, hx⟩ := by
    intro x hx
    rw [topologicalKrullDimAt_fiber_asFiber_eq_preimage f x]
    exact (topologicalKrullDimAt_preimage_congr (f : X → Y) hx.symm x hx rfl).symm
  rw [IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo s).isHomeomorph,
    TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  constructor
  · intro h x hx
    rw [key x hx, topologicalKrullDimAt_eq_localKrullDim]
    exact le_trans (le_iSup (fun w : (f : X → Y) ⁻¹' {s} ↦ localKrullDim _ w) ⟨x, hx⟩) h
  · intro h
    refine iSup_le fun w ↦ ?_
    rw [← topologicalKrullDimAt_eq_localKrullDim, ← key w.1 w.2]
    exact h w.1 w.2

/-! ### Fibre dimension in the limit -/

/-- Let `(φ_i : X_i ⟶ S_i)` be an inverse system of morphisms of schemes over a cofiltered index
category in the universe of the schemes, with the transition morphisms of the bases affine, the
bases quasi-compact, the `φ_i` of finite type, and the canonical morphisms
`X_i ⟶ X_j ×_{S_j} S_i` closed immersions. Let `F : lim X_i ⟶ lim S_i` be the limit morphism,
and assume moreover that the canonical morphisms `lim X_i ⟶ X_i ×_{S_i} lim S_j` are closed
immersions. If every fibre of `F` has dimension at most `d`, then so does every fibre of some
`φ_i`. -/
public theorem exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_cofiltered
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {X S : I ⥤ Scheme.{u}} (φ : X ⟶ S)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (S.map h)]
    [∀ i, CompactSpace (S.obj i)]
    [∀ i, LocallyOfFiniteType (φ.app i)] [∀ i, QuasiCompact (φ.app i)]
    [∀ {i j : I} (h : i ⟶ j),
      IsClosedImmersion (pullback.lift (X.map h) (φ.app i) (φ.naturality h))]
    {cX : Cone X} (hcX : IsLimit cX) {cS : Cone S} (hcS : IsLimit cS)
    {F : cX.pt ⟶ cS.pt} (hf : ∀ i, cX.π.app i ≫ φ.app i = F ≫ cS.π.app i)
    (hlim : ∀ i, IsClosedImmersion (pullback.lift (cX.π.app i) F (hf i)))
    (d : ℕ)
    (hdim : ∀ s : cS.pt, topologicalKrullDim (F.fiber s) ≤ (d : WithBot ℕ∞)) :
    ∃ i : I, ∀ s : S.obj i, topologicalKrullDim ((φ.app i).fiber s) ≤ (d : WithBot ℕ∞) := by
  classical
  have haff : ∀ {i j : I} (h : i ⟶ j), IsAffineHom (X.map h) := by
    intro i j h
    have h1 : X.map h = pullback.lift (X.map h) (φ.app i) (φ.naturality h) ≫
        pullback.fst (φ.app j) (S.map h) := (pullback.lift_fst _ _ _).symm
    have h2 : IsAffineHom (pullback.fst (φ.app j) (S.map h)) :=
      MorphismProperty.of_isPullback
        (IsPullback.of_hasPullback (φ.app j) (S.map h)).flip inferInstance
    rw [h1]
    infer_instance
  have hcpt : ∀ i, CompactSpace (X.obj i) := fun i ↦
    QuasiCompact.compactSpace_of_compactSpace (φ.app i)
  by_contra hcon
  simp only [not_exists, not_forall] at hcon
  set Z : ∀ i : I, Set (X.obj i) := fun i ↦
    {x | ¬ topologicalKrullDimAt ((φ.app i).fiber ((φ.app i) x)) ((φ.app i).asFiber x) ≤
      (d : WithBot ℕ∞)} with hZdef
  have hZc : ∀ i, IsClosed (Z i) := fun i ↦
    (isOpen_setOf_fiberDimensionAt_le (φ.app i) d).isClosed_compl
  have hZne : ∀ i, (Z i).Nonempty := by
    intro i
    obtain ⟨s, hs⟩ := hcon i
    rw [topologicalKrullDim_fiber_le_iff, not_forall] at hs
    obtain ⟨x, hx⟩ := hs
    exact ⟨x, (not_imp.mp hx).2⟩
  have hZcpt : ∀ i, IsCompact (Z i) := fun i ↦ (hZc i).isCompact
  have hmaps : ∀ {i j : I} (h : i ⟶ j), Set.MapsTo (X.map h) (Z i) (Z j) := by
    intro i j h x hx hbad
    exact hx ((topologicalKrullDimAt_fiber_le_of_isClosedImmersion_lift
      (φ.naturality h) x).trans hbad)
  obtain ⟨z, hz⟩ := exists_mem_of_isClosed_of_nonempty X cX hcX Z hZc hZne hZcpt hmaps
  set g : Spec (cS.pt.residueField (F z)) ⟶ cS.pt :=
    cS.pt.fromSpecResidueField (F z) with hgdef
  have hYci : ∀ {i j : I} (h : i ⟶ j), IsClosedImmersion ((baseChangeSystem φ g).map h) :=
    fun {_ _} h ↦ isClosedImmersion_baseChangeSystem_map φ g h
  have hYsnd : ∀ i : I, LocallyOfFiniteType (pullback.snd (φ.app i) (g ≫ cS.π.app i)) :=
    fun i ↦ MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (φ.app i) (g ≫ cS.π.app i)) inferInstance
  have hYqc : ∀ i : I, QuasiCompact (pullback.snd (φ.app i) (g ≫ cS.π.app i)) :=
    fun i ↦ MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (φ.app i) (g ≫ cS.π.app i)) inferInstance
  have hYcpt : ∀ i : I, CompactSpace ((baseChangeSystem φ g).obj i) := fun i ↦
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (φ.app i) (g ≫ cS.π.app i))
  have hYjac : ∀ i : I, JacobsonSpace ((baseChangeSystem φ g).obj i) := fun i ↦
    LocallyOfFiniteType.jacobsonSpace (pullback.snd (φ.app i) (g ≫ cS.π.app i))
  have hYnoe : ∀ i : I, NoetherianSpace ((baseChangeSystem φ g).obj i) := fun i ↦
    have : IsNoetherian ((baseChangeSystem φ g).obj i) := ⟨⟩
    inferInstance
  have hπ : ∀ j : I, IsClosedImmersion ((baseChangeSystemCone φ hf g).π.app j) := fun j ↦
    MorphismProperty.of_isPullback
      (isPullback_pullback_map_id F (φ.app j) (cX.π.app j) (cS.π.app j) (hf j).symm g
        (g ≫ cS.π.app j) rfl).flip (hlim j)
  obtain ⟨j, hj⟩ := exists_topologicalKrullDim_eq_of_isLimit (baseChangeSystem φ g)
    (baseChangeSystemCone φ hf g) (isLimitBaseChangeSystemCone φ hcX hcS hf g)
    (Nonempty.some IsCofiltered.nonempty) hπ
  have hYd : topologicalKrullDim ((baseChangeSystem φ g).obj j) ≤ (d : WithBot ℕ∞) := by
    rw [hj]; exact hdim (F z)
  obtain ⟨w, hwz⟩ : ∃ w : (baseChangeSystemCone φ hf g).pt, pullback.fst F g w = z :=
    ⟨F.asFiber z, F.fiberι_asFiber z⟩
  have hfst : pullback.fst (φ.app j) (g ≫ cS.π.app j)
      ((baseChangeSystemCone φ hf g).π.app j w) = cX.π.app j z := by
    have h1 : ((baseChangeSystemCone φ hf g).π.app j ≫
        pullback.fst (φ.app j) (g ≫ cS.π.app j)) w = (pullback.fst F g ≫ cX.π.app j) w :=
      congrArg (fun m : (baseChangeSystemCone φ hf g).pt ⟶ X.obj j ↦ m w)
        (baseChangeCone_π_fst φ hf g j)
    rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hwz] at h1
  set y := (baseChangeSystemCone φ hf g).π.app j w with hydef
  have hle : topologicalKrullDimAt ((pullback.snd (φ.app j) (g ≫ cS.π.app j)).fiber
        ((pullback.snd (φ.app j) (g ≫ cS.π.app j)) y))
      ((pullback.snd (φ.app j) (g ≫ cS.π.app j)).asFiber y) ≤ (d : WithBot ℕ∞) := by
    refine (topologicalKrullDimAt_le_topologicalKrullDim _).trans ?_
    rw [IsHomeomorph.topologicalKrullDim_eq _
      ((pullback.snd (φ.app j) (g ≫ cS.π.app j)).fiberHomeo _).isHomeomorph]
    exact (topologicalKrullDim_subspace_le _ _).trans hYd
  rw [topologicalKrullDimAt_fiber_eq_of_isPullback
    (IsPullback.of_hasPullback (φ.app j) (g ≫ cS.π.app j)) y, hfst] at hle
  exact hz j hle

/-- `AlgebraicGeometry.exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_cofiltered` with
the index universes independent of the universe of the schemes: the index category is only asked
to be locally `u`-small and to have a `u`-small initial subcategory. -/
public theorem exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_initiallySmall
    {I : Type uI} [Category.{v} I] [IsCofiltered I]
    [LocallySmall.{u} I] [InitiallySmall.{u} I]
    {X S : I ⥤ Scheme.{u}} (φ : X ⟶ S)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (S.map h)]
    [∀ i, CompactSpace (S.obj i)]
    [∀ i, LocallyOfFiniteType (φ.app i)] [∀ i, QuasiCompact (φ.app i)]
    [∀ {i j : I} (h : i ⟶ j),
      IsClosedImmersion (pullback.lift (X.map h) (φ.app i) (φ.naturality h))]
    {cX : Cone X} (hcX : IsLimit cX) {cS : Cone S} (hcS : IsLimit cS)
    {F : cX.pt ⟶ cS.pt} (hf : ∀ i, cX.π.app i ≫ φ.app i = F ≫ cS.π.app i)
    (hlim : ∀ i, IsClosedImmersion (pullback.lift (cX.π.app i) F (hf i)))
    (d : ℕ)
    (hdim : ∀ s : cS.pt, topologicalKrullDim (F.fiber s) ≤ (d : WithBot ℕ∞)) :
    ∃ i : I, ∀ s : S.obj i, topologicalKrullDim ((φ.app i).fiber s) ≤ (d : WithBot ℕ∞) := by
  have hX : ∀ {a b : CofilteredInitialModel.{u} I} (k : a ⟶ b),
      IsClosedImmersion (pullback.lift ((fromCofilteredInitialModel.{u} I ⋙ X).map k)
        ((Functor.whiskerLeft (fromCofilteredInitialModel.{u} I) φ).app a)
        ((Functor.whiskerLeft (fromCofilteredInitialModel.{u} I) φ).naturality k)) := by
    intro a b k; dsimp; infer_instance
  have hS : ∀ {a b : CofilteredInitialModel.{u} I} (k : a ⟶ b),
      IsAffineHom ((fromCofilteredInitialModel.{u} I ⋙ S).map k) := by
    intro a b k; dsimp; infer_instance
  have hcpt : ∀ a : CofilteredInitialModel.{u} I,
      CompactSpace ((fromCofilteredInitialModel.{u} I ⋙ S).obj a) := by
    intro a; dsimp; infer_instance
  have hft : ∀ a : CofilteredInitialModel.{u} I,
      LocallyOfFiniteType
        ((Functor.whiskerLeft (fromCofilteredInitialModel.{u} I) φ).app a) := by
    intro a; dsimp; infer_instance
  have hqc : ∀ a : CofilteredInitialModel.{u} I,
      QuasiCompact
        ((Functor.whiskerLeft (fromCofilteredInitialModel.{u} I) φ).app a) := by
    intro a; dsimp; infer_instance
  obtain ⟨a, ha⟩ := exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_cofiltered
    (I := CofilteredInitialModel.{u} I)
    (Functor.whiskerLeft (fromCofilteredInitialModel.{u} I) φ)
    ((Functor.Initial.isLimitWhiskerEquiv
      (fromCofilteredInitialModel.{u} I) cX).symm hcX)
    ((Functor.Initial.isLimitWhiskerEquiv
      (fromCofilteredInitialModel.{u} I) cS).symm hcS)
    (F := F) (fun a ↦ hf _) (fun a ↦ hlim _) d hdim
  exact ⟨_, ha⟩

/-- Let `(φ_i : X_i ⟶ S_i)` be an inverse system of morphisms of schemes over a cofiltered index
category with a `u`-small initial subcategory, with the transition morphisms of the bases affine,
the bases quasi-compact and quasi-separated, the `φ_i` of finite type, and the canonical morphisms
`X_i ⟶ X_j ×_{S_j} S_i` closed immersions, and assume that the canonical morphisms
`lim X_i ⟶ X_i ×_{S_i} lim S_j` are closed immersions. If every fibre of the canonical morphism
`lim X_i ⟶ lim S_i` has dimension at most `d`, then so does every fibre of some `φ_i`. -/
public theorem exists_forall_topologicalKrullDim_fiber_le_of_isLimit
    {I : Type uI} [Category.{v} I] [IsCofiltered I]
    [LocallySmall.{u} I] [InitiallySmall.{u} I]
    (X S : I ⥤ Scheme.{u}) (φ : X ⟶ S)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (S.map h)]
    [∀ i, CompactSpace (S.obj i)] [∀ i, QuasiSeparatedSpace (S.obj i)]
    [∀ i, LocallyOfFiniteType (φ.app i)] [∀ i, QuasiCompact (φ.app i)]
    [∀ {i j : I} (h : i ⟶ j),
      IsClosedImmersion (pullback.lift (X.map h) (φ.app i) (φ.naturality h))]
    (cX : Cone X) (hcX : IsLimit cX) (cS : Cone S) (hcS : IsLimit cS) (d : ℕ)
    (hlim : ∀ i, IsClosedImmersion (pullback.lift (cX.π.app i)
      (hcS.lift ((Cone.postcompose φ).obj cX))
      ((hcS.fac ((Cone.postcompose φ).obj cX) i).symm)))
    (hdim : ∀ s : cS.pt,
      topologicalKrullDim ((hcS.lift ((Cone.postcompose φ).obj cX)).fiber s) ≤
        (d : WithBot ℕ∞)) :
    ∃ i : I, ∀ s : S.obj i,
      topologicalKrullDim ((φ.app i).fiber s) ≤ (d : WithBot ℕ∞) :=
  exists_forall_topologicalKrullDim_fiber_le_of_isLimit_of_initiallySmall φ hcX hcS
    (fun i ↦ (hcS.fac ((Cone.postcompose φ).obj cX) i).symm) hlim d hdim

end AlgebraicGeometry

end
