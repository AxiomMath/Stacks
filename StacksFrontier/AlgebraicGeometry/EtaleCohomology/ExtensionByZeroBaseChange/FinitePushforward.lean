module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Pushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.SplitSections
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.CategoryTheory.Sites.SurjectivityFromGraphCover
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono
public import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero agrees with the direct image along a finite étale morphism

Let `j : U ⟶ X` be finite and étale, viewed as an object of the small étale site of `X`. The
comparison map `j_! ⟶ j_*` is always injective; it is an isomorphism exactly because a finite
étale morphism is, étale-locally on the base, a finite disjoint union of copies of the base.

Locally on `X`, then, the `Q`-points of `U` over `X` are finitely many morphisms
`φ_1, …, φ_n : Q ⟶ U`, pairwise disjoint and with graphs covering `Q ×_X U`. The summand of
`j_!F` indexed by `φ_i` maps to the section of `F` over `Q ×_X U` which is the given one on the
graph of `φ_i` and zero off it, so a section of `j_*F` over `Q` is the image of the sum of the
summands indexed by its restrictions to the `n` graphs: restricting that sum back along the
`i`-th graph returns the `i`-th restriction, every other summand vanishing there by
disjointness. Hence the comparison is surjective locally on `X`, and being injective it is an
isomorphism.

## Main results

* `AlgebraicGeometry.abelianExtensionByZeroToPushforward_isIso` and
  `AlgebraicGeometry.moduleExtensionByZeroToPushforward_isIso` — the comparison map `j_! ⟶ j_*`
  is an isomorphism for abelian sheaves and for sheaves of `Λ`-modules.
* `AlgebraicGeometry.exists_smallEtaleArrows_cover` — the local description of `U` as finitely
  many pairwise disjoint morphisms from an étale neighbourhood, with graphs covering the base
  change.
* `AlgebraicGeometry.disjointFromSmallEtaleGraph_smallEtaleLiftGraph` — disjoint morphisms
  `Q ⟶ U` have graphs disjoint in the étale-test-object sense.
* `AlgebraicGeometry.map_smallEtaleLiftGraph_eq` — the graph of `φ : Q ⟶ U` is the unique
  section of `Q ×_X U ⟶ Q` whose other component is `φ`.
* `AlgebraicGeometry.smallEtaleArrowsDisjoint_of_isEmpty` and
  `AlgebraicGeometry.isEmpty_of_sheet_comp_snd_eq` — the two halves of the disjointness of two
  distinct sheets, read as morphisms `Q ⟶ U`.

## Implementation notes

The fibre product `Q ×_X U` of the small étale site is the slice-category pullback, and the
identification of its underlying scheme with the fibre product of the structure morphisms is
not available to the elaborator, because the chosen limit cone behind `pullback.fst` is not
exposed. `AlgebraicGeometry.map_smallEtaleLiftGraph_eq`, which is the one statement here that
mentions both spellings, therefore relaxes transparency; everything else is phrased on one side
of the identification.

## References

* [Stacks Project, Tag 03S7](https://stacks.math.columbia.edu/tag/03S7)
* [Stacks Project, Tag 0F4L](https://stacks.math.columbia.edu/tag/0F4L)
* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (U : SmallEtale B X hX)

/-- The graph of a morphism `ψ : V ⟶ U`, transported into the base change of `V`, avoids the
graph of a morphism `φ : V ⟶ U` disjoint from it: a test object mapping to both would identify
the underlying morphisms of `φ` and `ψ` on it. -/
public theorem disjointFromSmallEtaleGraph_smallEtaleLiftGraph
    (V : SmallEtale B X hX) (φ ψ : V ⟶ U)
    (h : smallEtaleArrowsDisjoint B X hX U V φ ψ) :
    disjointFromSmallEtaleGraph B X hX U (smallEtaleLift B X hX U V φ)
      (smallEtaleLift B X hX U V ψ)
      (smallEtaleLiftGraph B X hX U V ψ ≫
        (smallEtaleBaseChange B U.obj.hom).map
          (smallEtaleLiftPostIso B X hX U V φ).inv) := by
  intro T hn a b hab
  have hh := congrArg (· ≫
    (smallEtaleBaseChange B U.obj.hom).map
      (smallEtaleLiftPostIso B X hX U V φ).hom) hab
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id] at hh
  exact h T hn a b ((smallEtaleLiftGraph_comp_eq_iff B X hX U V φ ψ T a b).mp hh)

/-- The graph of `φ : Q ⟶ U` is the unique section of the first projection of `Q ×_X U` whose
composite with the second projection is `φ`. -/
public theorem map_smallEtaleLiftGraph_eq
    (Q : SmallEtale B X hX) (φ : Q ⟶ U)
    (s : B.inclusion.obj Q.obj.left ⟶ B.inclusion.obj (pullback Q.obj.hom U.obj.hom))
    (h₁ : s ≫ B.inclusion.map (pullback.fst Q.obj.hom U.obj.hom) = 𝟙 _)
    (h₂ : s ≫ B.inclusion.map (pullback.snd Q.obj.hom U.obj.hom) =
      B.inclusion.map φ.hom.left) :
    B.inclusion.map (smallEtaleLiftGraph B X hX U Q φ).hom.left = s := by
  -- Both projections are compared in term mode. The codomain of the transported graph is
  -- `((smallEtaleBaseChange B U.obj.hom).obj Q).obj.left`, which is the fibre product
  -- `pullback Q.obj.hom U.obj.hom` under a different name; `rw` cannot see through that, so the
  -- functoriality steps are chained with `Eq.trans` instead.
  refine ((IsPullback.of_hasPullback Q.obj.hom U.obj.hom).map B.inclusion).hom_ext ?_ ?_
  · exact ((B.inclusion.map_comp (smallEtaleLiftGraph B X hX U Q φ).hom.left
        (pullback.fst Q.obj.hom U.obj.hom)).symm.trans
      ((congrArg B.inclusion.map (smallEtaleLiftGraph_fst B X hX U Q φ)).trans
        (B.inclusion.map_id _))).trans h₁.symm
  · exact ((B.inclusion.map_comp (smallEtaleLiftGraph B X hX U Q φ).hom.left
        (pullback.snd Q.obj.hom U.obj.hom)).symm.trans
      (congrArg B.inclusion.map (smallEtaleLiftGraph B X hX U Q φ).hom.w)).trans h₂.symm

/-- Morphisms `Q ⟶ U` which agree after restriction to a scheme `Z` are disjoint as soon as no
such `Z` is nonempty. -/
public theorem smallEtaleArrowsDisjoint_of_isEmpty
    (Q : SmallEtale B X hX) (φ ψ : Q ⟶ U)
    (hemp : ∀ {Z : Scheme.{u}} (c : Z ⟶ B.inclusion.obj Q.obj.left),
      c ≫ B.inclusion.map φ.hom.left = c ≫ B.inclusion.map ψ.hom.left → IsEmpty Z) :
    smallEtaleArrowsDisjoint B X hX U Q φ ψ := by
  intro S hns a b hab
  have hφ : a.hom.left ≫ φ.hom.left = a.hom.left ≫ ψ.hom.left :=
    calc a.hom.left ≫ φ.hom.left = S.obj.hom := a.hom.w
      _ = b.hom.left ≫ ψ.hom.left := b.hom.w.symm
      _ = a.hom.left ≫ ψ.hom.left := congrArg (· ≫ ψ.hom.left) hab.symm
  refine (hemp (B.inclusion.map a.hom.left) ?_).elim hns.some
  exact (Functor.map_comp B.inclusion a.hom.left φ.hom.left).symm.trans
    ((congrArg B.inclusion.map hφ).trans
      (Functor.map_comp B.inclusion a.hom.left ψ.hom.left))

/-- A scheme over which two distinct sheets of `V ×_X U ⟶ V` have the same composite with the
projection to `U` is empty: the two sheets then agree on it. -/
public theorem isEmpty_of_sheet_comp_snd_eq
    (V : SmallEtale B X hX) {N : Scheme.{u}} {g : N ⟶ B.inclusion.obj V.obj.left}
    (hsp : Stacks.Etale.IsSplitOver
      (B.inclusion.map (pullback.fst V.obj.hom U.obj.hom)) g)
    {i j : hsp.I} (hij : i ≠ j) {Z : Scheme.{u}} (c : Z ⟶ N)
    (hc : c ≫ hsp.sheet i ≫ B.inclusion.map (pullback.snd V.obj.hom U.obj.hom) =
      c ≫ hsp.sheet j ≫ B.inclusion.map (pullback.snd V.obj.hom U.obj.hom)) :
    IsEmpty Z := by
  refine hsp.isEmpty_of_sheet_eq c hij ?_
  refine ((IsPullback.of_hasPullback V.obj.hom U.obj.hom).map B.inclusion).hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hsp.sheet_comp, hsp.sheet_comp]
  · rwa [Category.assoc, Category.assoc]

/-- A morphism `q₀ : Q ⟶ V` over `X` induces a map `Q ×_X U ⟶ V ×_X U` over `U` which makes the
square with the first projections a pullback. -/
public theorem exists_isPullback_pullback_of_hom_eq_comp
    (Q V : SmallEtale B X hX) (q₀ : Q.obj.left ⟶ V.obj.left) (h : Q.obj.hom = q₀ ≫ V.obj.hom) :
    ∃ α : pullback Q.obj.hom U.obj.hom ⟶ pullback V.obj.hom U.obj.hom,
      α ≫ pullback.snd V.obj.hom U.obj.hom = pullback.snd Q.obj.hom U.obj.hom ∧
      IsPullback α (pullback.fst Q.obj.hom U.obj.hom) (pullback.fst V.obj.hom U.obj.hom) q₀ := by
  let α : pullback Q.obj.hom U.obj.hom ⟶ pullback V.obj.hom U.obj.hom :=
    pullback.lift (pullback.fst Q.obj.hom U.obj.hom ≫ q₀) (pullback.snd Q.obj.hom U.obj.hom)
      (by rw [Category.assoc, ← h]; exact pullback.condition)
  have hα₁ : α ≫ pullback.fst V.obj.hom U.obj.hom =
      pullback.fst Q.obj.hom U.obj.hom ≫ q₀ := pullback.lift_fst _ _ _
  have hα₂ : α ≫ pullback.snd V.obj.hom U.obj.hom =
      pullback.snd Q.obj.hom U.obj.hom := pullback.lift_snd _ _ _
  refine ⟨α, hα₂,
    IsPullback.of_right ?_ hα₁ (IsPullback.of_hasPullback V.obj.hom U.obj.hom).flip⟩
  rw [hα₂, ← h]
  exact (IsPullback.of_hasPullback Q.obj.hom U.obj.hom).flip

variable [IsFinite (B.inclusion.map U.obj.hom)]

/-- Étale-locally on `X`, the structure morphism of `U` is a finite disjoint union of
isomorphisms: every point of an étale object `V` over `X` has an étale neighbourhood `Q ⟶ V`
over which `U` is described by finitely many pairwise disjoint morphisms `Q ⟶ U` whose graphs
cover `Q ×_X U`. The neighbourhood is the one supplied by the sheet data of the finite étale
morphism `V ×_X U ⟶ V`, and the morphisms `Q ⟶ U` are its sheets read as `Q`-points of `U`. -/
public theorem exists_smallEtaleArrows_cover
    (V : SmallEtale B X hX) (x : V.obj.left.1) :
    ∃ (Q : SmallEtale B X hX) (q : Q ⟶ V),
      x ∈ Set.range (B.inclusion.map q.hom.left) ∧
      ∃ (ι : Type u) (_ : Finite ι) (φ : ι → (Q ⟶ U)),
        (∀ z : ((smallEtaleBaseChange B U.obj.hom).obj Q).obj.left.1,
            ∃ i, z ∈ Set.range (B.inclusion.map
              (smallEtaleLiftGraph B X hX U Q (φ i)).hom.left)) ∧
        Pairwise (fun i j => smallEtaleArrowsDisjoint B X hX U Q (φ i) (φ j)) := by
  classical
  have hVU := (IsPullback.of_hasPullback V.obj.hom U.obj.hom).map B.inclusion
  have hfin : IsFinite (B.inclusion.map (pullback.fst V.obj.hom U.obj.hom)) :=
    MorphismProperty.of_isPullback hVU.flip inferInstance
  have hEt : Etale (B.inclusion.map (pullback.fst V.obj.hom U.obj.hom)) :=
    MorphismProperty.of_isPullback hVU.flip inferInstance
  obtain ⟨N, g, _, _, n, hn, ⟨hsp⟩⟩ :=
    Stacks.Etale.exists_compactSpace_etale_isSplitOver
      (B.inclusion.map (pullback.fst V.obj.hom U.obj.hom)) x
  have hN : B.Contains N :=
    (Scheme.size_le_of_locallyOfFiniteType g).trans_lt V.obj.left.property
  let q₀ : B.obj N hN ⟶ V.obj.left := ObjectProperty.homMk g
  let Q : SmallEtale B X hX :=
    ⟨Over.mk (q₀ ≫ V.obj.hom), inferInstanceAs (Etale (g ≫ B.inclusion.map V.obj.hom))⟩
  let q : Q ⟶ V := ObjectProperty.homMk (Over.homMk q₀ rfl)
  obtain ⟨α, hα₂, hsqB⟩ := exists_isPullback_pullback_of_hom_eq_comp B X hX U Q V q₀ rfl
  have hsq := hsqB.map B.inclusion
  let σ (i : hsp.I) := hsp.sectionOfIsPullback hsq i
  have hσfst (i : hsp.I) :
      σ i ≫ B.inclusion.map (pullback.fst Q.obj.hom U.obj.hom) = 𝟙 _ :=
    hsp.sectionOfIsPullback_comp_snd hsq i
  let σ' (i : hsp.I) : Q.obj.left ⟶ pullback Q.obj.hom U.obj.hom :=
    ObjectProperty.homMk (σ i)
  have hfst (i : hsp.I) : σ' i ≫ pullback.fst Q.obj.hom U.obj.hom = 𝟙 Q.obj.left := by
    apply B.inclusion.map_injective
    simp only [Functor.map_comp, CategoryTheory.Functor.map_id]
    exact hσfst i
  let φ (i : hsp.I) : Q ⟶ U := ObjectProperty.homMk (Over.homMk
    (σ' i ≫ pullback.snd Q.obj.hom U.obj.hom) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hfst i, Category.id_comp]))
  have hσsnd (i : hsp.I) : σ i ≫ B.inclusion.map (pullback.snd Q.obj.hom U.obj.hom) =
      B.inclusion.map (φ i).hom.left :=
    (Functor.map_comp B.inclusion (σ' i) (pullback.snd Q.obj.hom U.obj.hom)).symm
  have hsheet (i : hsp.I) :
      hsp.sheet i ≫ B.inclusion.map (pullback.snd V.obj.hom U.obj.hom) =
        σ i ≫ B.inclusion.map (pullback.snd Q.obj.hom U.obj.hom) := by
    rw [← hsp.sectionOfIsPullback_comp_fst hsq i, Category.assoc, ← Functor.map_comp, hα₂]
  refine ⟨Q, q, ⟨n, hn⟩, hsp.I, hsp.finite_I, φ, ?_, ?_⟩
  · intro z
    obtain ⟨i, hi⟩ := hsp.exists_mem_range_sectionOfIsPullback hsq z
    exact ⟨i, by rwa [map_smallEtaleLiftGraph_eq B X hX U Q (φ i) (σ i) (hσfst i) (hσsnd i)]⟩
  · intro i j hij
    refine smallEtaleArrowsDisjoint_of_isEmpty B X hX U Q (φ i) (φ j) fun c hcc => ?_
    exact isEmpty_of_sheet_comp_snd_eq B X hX U V hsp hij c
      (by rwa [hsheet i, hsheet j, hσsnd i, hσsnd j])

/-- The canonical map from extension by zero to the direct image is locally surjective on
abelian sheaves, for a finite étale morphism. -/
public theorem abelianExtensionByZeroToPushforward_app_isLocallySurjective
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}) :
    Sheaf.IsLocallySurjective ((abelianExtensionByZeroToPushforward B X hX U).app F) := by
  have : IsSeparated (B.inclusion.map U.obj.hom) := IsSeparated.of_isAffineHom _
  let θ := (abelianExtensionByZeroToPushforward B X hX U).app F
  constructor
  intro V s
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  obtain ⟨Q, q, hx, ι, _, φ, hcov, hd⟩ := exists_smallEtaleArrows_cover B X hX U V x
  have hsurj := Presheaf.surjective_app_of_graphCover
    (smallEtalePostcompose B X hX U)
    (smallEtaleBaseChange B U.obj.hom)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property) F.obj F.isSeparated
    ((abelianExtensionByZero B X hX U).obj F).obj θ.hom
    (fun W => ((abelianExtensionByZeroAdjunction B X hX U).unit.app F).hom.app
      (Opposite.op W))
    (smallEtaleGraph B X hX U)
    (abelianExtensionByZeroToPushforward_graph B X hX U F)
    (fun i => smallEtaleLift B X hX U Q (φ i))
    (fun i => smallEtaleLiftPostIso B X hX U Q (φ i))
    (SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective
      B U.obj.left.1 U.obj.left.property _ _ hcov)
    (fun i j hij =>
      abelianExtensionByZeroToPushforward_graph_compl B X hX U F _ _ _
        (disjointFromSmallEtaleGraph_smallEtaleLiftGraph B X hX U Q (φ i) (φ j) (hd hij)))
  exact ⟨Q, q, hsurj _, hx⟩

/-- A monomorphism of sheaves which is locally surjective is an isomorphism, in a concrete
category where monomorphisms are injective. -/
private theorem isIso_of_mono_of_isLocallySurjective {C : Type*} [Category C]
    {J : GrothendieckTopology C} {A : Type*} [Category A] {FA : A → A → Type*}
    {CA : A → Type*} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
    [(forget A).ReflectsIsomorphisms] [J.HasSheafCompose (forget A)]
    [(sheafToPresheaf J A).PreservesMonomorphisms] [HasLimits A] {F G : Sheaf J A}
    (θ : F ⟶ G) [Mono θ] [Sheaf.IsLocallySurjective θ]
    (h : ∀ {Y Z : A} (f : Y ⟶ Z), Mono f → Function.Injective f) : IsIso θ := by
  have : Mono θ.hom := (sheafToPresheaf _ _).map_mono θ
  have hinj : Sheaf.IsLocallyInjective θ :=
    Presheaf.isLocallyInjective_of_injective _ _ fun Y => h _ inferInstance
  exact (Sheaf.isLocallyBijective_iff_isIso θ).mp ⟨hinj, inferInstance⟩

/-- **Stacks 03S7.** For a finite étale morphism, the canonical map from extension by zero to
the direct image is an isomorphism on abelian sheaves. -/
@[stacks 03S7 "abelian sheaves"]
public theorem abelianExtensionByZeroToPushforward_isIso :
    IsIso (abelianExtensionByZeroToPushforward B X hX U) := by
  have h (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      AddCommGrpCat.{u + 1}) :
      IsIso ((abelianExtensionByZeroToPushforward B X hX U).app F) := by
    have : Mono ((abelianExtensionByZeroToPushforward B X hX U).app F) :=
      abelianExtensionByZeroToPushforward_mono B X hX U F
    have : Sheaf.IsLocallySurjective ((abelianExtensionByZeroToPushforward B X hX U).app F) :=
      abelianExtensionByZeroToPushforward_app_isLocallySurjective B X hX U F
    exact isIso_of_mono_of_isLocallySurjective _ fun f => (AddCommGrpCat.mono_iff_injective f).mp
  exact NatIso.isIso_of_isIso_app _

/-- The canonical map from extension by zero to the direct image is locally surjective on
sheaves of `Λ`-modules, for a finite étale morphism. -/
public theorem moduleExtensionByZeroToPushforward_app_isLocallySurjective (Λ : Type v) [Ring Λ]
    (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) v} Λ)) :
    Sheaf.IsLocallySurjective ((moduleExtensionByZeroToPushforward B X hX U Λ).app F) := by
  have : IsSeparated (B.inclusion.map U.obj.hom) := IsSeparated.of_isAffineHom _
  let θ := (moduleExtensionByZeroToPushforward B X hX U Λ).app F
  let A := forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v}
  let F' := (sheafCompose
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property) A).obj F
  constructor
  intro V s
  apply SmallEtale.mem_topology_of_jointlySurjective
  intro x
  obtain ⟨Q, q, hx, ι, _, φ, hcov, hd⟩ := exists_smallEtaleArrows_cover B X hX U V x
  have hsurj := Presheaf.surjective_app_of_graphCover
    (smallEtalePostcompose B X hX U)
    (smallEtaleBaseChange B U.obj.hom)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property) F'.obj F'.isSeparated
    (((moduleExtensionByZero B X hX U Λ).obj F).obj ⋙ A)
    (Functor.whiskerRight θ.hom A)
    (fun W => A.map (((moduleExtensionByZeroAdjunction B X hX U Λ).unit.app F).hom.app
      (Opposite.op W)))
    (smallEtaleGraph B X hX U)
    (moduleExtensionByZeroToPushforward_graph B X hX U Λ F)
    (fun i => smallEtaleLift B X hX U Q (φ i))
    (fun i => smallEtaleLiftPostIso B X hX U Q (φ i))
    (SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective
      B U.obj.left.1 U.obj.left.property _ _ hcov)
    (fun i j hij =>
      moduleExtensionByZeroToPushforward_graph_compl B X hX U Λ F _ _ _
        (disjointFromSmallEtaleGraph_smallEtaleLiftGraph B X hX U Q (φ i) (φ j) (hd hij)))
  exact ⟨Q, q, hsurj _, hx⟩

/-- **Stacks 03S7.** For a finite étale morphism, the canonical map from extension by zero to
the direct image is an isomorphism on sheaves of `Λ`-modules. -/
@[stacks 03S7 "sheaves of modules"]
public theorem moduleExtensionByZeroToPushforward_isIso (Λ : Type v) [Ring Λ] :
    IsIso (moduleExtensionByZeroToPushforward B X hX U Λ) := by
  have h (F : Sheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
      (ModuleCat.{max (u + 1) v} Λ)) :
      IsIso ((moduleExtensionByZeroToPushforward B X hX U Λ).app F) := by
    have : Mono ((moduleExtensionByZeroToPushforward B X hX U Λ).app F) :=
      moduleExtensionByZeroToPushforward_mono B X hX U Λ F
    have : Sheaf.IsLocallySurjective ((moduleExtensionByZeroToPushforward B X hX U Λ).app F) :=
      moduleExtensionByZeroToPushforward_app_isLocallySurjective B X hX U Λ F
    exact isIso_of_mono_of_isLocallySurjective _ fun f => (ModuleCat.mono_iff_injective f).mp
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry

end
