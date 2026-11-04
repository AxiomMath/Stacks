module

public import Mathlib.CategoryTheory.ConnectedComponents
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Colimits over an almost-directed category commute with finite connected limits

A category `I` is almost directed if every connected component of `I` is filtered. For such an
`I` whose type of objects is `v`-small, the colimit functor `colim : (I ⥤ Type v) ⥤ Type v`
commutes with finite connected limits, in particular with fibre products and equalizers.

The colimit functor factors, up to natural isomorphism, as
`colim ≅ componentColimFunctor ⋙ sigmaTypeFunctor`: a colimit in `Type v` is the disjoint union
over the connected components `c` of `I` of the colimits over `c`. The first factor preserves
finite limits because each component is filtered; the second preserves connected limits, since
the index coordinate of a compatible family is constant along a connected shape. Connectedness is
needed: for the discrete two-object shape the claim would read
`Σ_c (A_c × B_c) ≅ (Σ_c A_c) × (Σ_c B_c)`.

## Main definitions

* `CategoryTheory.Limits.IsAlmostDirected`: every connected component of the category is filtered.

## Main results

* `CategoryTheory.Limits.preservesLimitsOfShape_colim_of_isConnected`: colimits over an
  almost-directed category commute with limits of every finite connected shape.
* `CategoryTheory.Limits.preservesLimitsOfShape_walkingCospan_colim` and
  `CategoryTheory.Limits.preservesLimitsOfShape_walkingParallelPair_colim`: they commute with fibre
  products and equalizers.

## References

* [Stacks 002Y](https://stacks.math.columbia.edu/tag/002Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-- Transporting the second component of a dependent pair along an equality of indices leaves
the pair unchanged. -/
theorem Sigma.mk_eqRec {α : Type*} {β : α → Type*} {a b : α} (h : a = b) (x : β a) :
    (⟨b, h ▸ x⟩ : Σ a, β a) = ⟨a, x⟩ := by
  subst h; rfl

/-- A family of maps `m` turns an equality `⟨a, m a x⟩ = ⟨b, z⟩` of dependent pairs into the
equality `m b (h ▸ x) = z` of elements of the fibre over `b`. -/
theorem Sigma.eq_of_mk_map_eq {α : Type*} {β γ : α → Type*} (m : ∀ a, β a → γ a) {a b : α}
    (h : a = b) (x : β a) {z : γ b} (hz : (⟨a, m a x⟩ : Σ a, γ a) = ⟨b, z⟩) :
    m b (h ▸ x) = z := by
  subst h; exact eq_of_heq (Sigma.ext_iff.mp hz).2

namespace CategoryTheory.Limits

universe v' v u w

section Decomposition

variable {I : Type u} [Category.{v'} I] [Small.{v} I]

/-- The type of connected components of a `v`-small category is `v`-small. -/
instance small_connectedComponents : Small.{v} (ConnectedComponents I) := by
  change Small.{v} (Quotient _); infer_instance

/-- Each connected component of a `v`-small category is `v`-small. -/
private instance small_component (c : ConnectedComponents I) :
    Small.{v} (ConnectedComponents.Component c) := by
  have hsub : Small.{v} {x : I // c.objectProperty x} := small_subtype (α := I) c.objectProperty
  exact small_map (α := ConnectedComponents.Component c)
    (e := { toFun := fun a => (⟨a.obj, a.property⟩ : {x : I // c.objectProperty x}),
            invFun := fun a => ⟨a.val, a.property⟩,
            left_inv := fun _ => rfl, right_inv := fun _ => rfl })

/-- The decomposed category `Decomposed I = Σ c, Component c` is `Small.{v}`. -/
private instance small_decomposed : Small.{v} (Decomposed I) :=
  small_sigma (fun c : ConnectedComponents I => c.Component)

/-- The functor sending `F : I ⥤ Type v` to the family `c ↦ colim (c.ι ⋙ F)` of colimits over
the connected components of `I`. -/
noncomputable def componentColimFunctor :
    (I ⥤ Type v) ⥤ (ConnectedComponents I → Type v) where
  obj F := fun c => colim.obj (c.ι ⋙ F)
  map {F G} η := fun c => colim.map (Functor.whiskerLeft c.ι η)
  map_id := by
    intro X
    funext c
    exact colim.map_id _
  map_comp := by
    intro X Y Z f g
    funext c
    rw [Functor.whiskerLeft_comp, colim.map_comp]
    rfl

/-- The functor sending a family `g : ConnectedComponents I → Type v` to the coproduct
`Σ c, g c`, shrunk to `Type v`, and a morphism `φ` to `⟨c, x⟩ ↦ ⟨c, φ c x⟩`. -/
@[implicit_reducible]
noncomputable def sigmaTypeFunctor :
    (ConnectedComponents I → Type v) ⥤ Type v where
  obj g := Shrink.{v} (Σ c, g c)
  map {g h} φ := ↾(fun (s : Shrink.{v} (Σ c, g c)) =>
    match (equivShrink (Σ c, g c)).symm s with
    | ⟨c, x⟩ => equivShrink (Σ c, h c) (⟨c, φ c x⟩ : Σ c, h c))
  map_id := by
    intro X
    apply ConcreteCategory.hom_ext
    intro s
    simp
  map_comp := by
    intro X Y Z f g
    apply ConcreteCategory.hom_ext
    intro s
    simp only [TypeCat.ofHom_apply, types_comp_apply]
    rw [Equiv.symm_apply_apply]
    rfl

/-- For `G : Decomposed I ⥤ Type v`, the cocone on `G` whose point is the (shrunk)
disjoint union `Σ c, colimit (Sigma.incl c ⋙ G)` of the colimits over the components. -/
private noncomputable def colimitDecomposedCocone (G : (Decomposed I) ⥤ Type v) : Cocone G where
  pt := Shrink.{v} (Σ c, colimit (Sigma.incl c ⋙ G))
  ι := { app := fun ⟨b, x⟩ => ↾(fun g =>
            equivShrink _ (⟨b, (colimit.ι (Sigma.incl b ⋙ G) x) g⟩ :
              Σ c, colimit (Sigma.incl c ⋙ G)))
         naturality := by
           rintro ⟨b, x⟩ ⟨b', x'⟩ ⟨f⟩
           apply ConcreteCategory.hom_ext
           intro g
           rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
           simp only [TypeCat.ofHom_apply, Functor.const_obj_map]
           rw [← colimit.w_apply (Sigma.incl b ⋙ G) f g]; rfl }

/-- The underlying function of the descent map out of `colimitDecomposedCocone`. -/
private noncomputable def colimitDecomposedDescFun (G : (Decomposed I) ⥤ Type v) (s : Cocone G) :
    (Σ c, colimit (Sigma.incl c ⋙ G)) → s.pt :=
  fun ⟨c, x⟩ => colimit.desc (Sigma.incl c ⋙ G) (s.whisker (Sigma.incl c)) x

/-- The cocone leg of `colimitDecomposedCocone G` at `⟨b, x⟩` sends `g` to the class of
`colimit.ι _ x g` in the `b`-th summand. -/
private lemma colimitDecomposedCocone_ι_app_apply (G : (Decomposed I) ⥤ Type v) (b : _)
    (x : _) (g : (Sigma.incl b ⋙ G).obj x) : (colimitDecomposedCocone G).ι.app ⟨b, x⟩ g
      = equivShrink _ (⟨b, (colimit.ι (Sigma.incl b ⋙ G) x) g⟩ :
        Σ c, colimit (Sigma.incl c ⋙ G)) := rfl

/-- The descent function restricted to a leg of `colimitDecomposedCocone G` is the corresponding
leg of `s`. -/
private lemma colimitDecomposedDescFun_ι_app (G : (Decomposed I) ⥤ Type v) (s : Cocone G)
    (b : _) (x : _) (g : (Sigma.incl b ⋙ G).obj x) :
    colimitDecomposedDescFun G s
      ((equivShrink _).symm ((colimitDecomposedCocone G).ι.app ⟨b, x⟩ g))
      = s.ι.app ⟨b, x⟩ g := by
  rw [colimitDecomposedCocone_ι_app_apply, Equiv.symm_apply_apply]
  change colimit.desc (Sigma.incl b ⋙ G) (s.whisker (Sigma.incl b)) _ = _
  rw [colimit.ι_desc_apply]; rfl

set_option backward.isDefEq.respectTransparency false in
/-- `colimitDecomposedCocone G` is a colimit cocone: the colimit over the sigma category
splits as the disjoint union of the colimits over each component. -/
private noncomputable def isColimitColimitDecomposedCocone (G : (Decomposed I) ⥤ Type v) :
    IsColimit (colimitDecomposedCocone G) where
  desc s := ↾(fun sh => colimitDecomposedDescFun G s ((equivShrink _).symm sh))
  fac := by
    rintro s ⟨b, x⟩
    apply ConcreteCategory.hom_ext
    intro g
    rw [ConcreteCategory.comp_apply]
    exact colimitDecomposedDescFun_ι_app G s b x g
  uniq := by
    intro s m hm
    apply ConcreteCategory.hom_ext
    intro sh
    set p := (equivShrink (Σ c, colimit (Sigma.incl c ⋙ G))).symm sh with hp
    obtain ⟨x, g, hg⟩ := Types.jointly_surjective' (F := Sigma.incl p.1 ⋙ G) p.2
    have key : (⟨p.1, (colimit.ι (Sigma.incl p.1 ⋙ G) x) g⟩ :
        Σ c, colimit (Sigma.incl c ⋙ G)) = p := by rw [hg]
    have hsh2 : sh = (colimitDecomposedCocone G).ι.app ⟨p.1, x⟩ g := by
      rw [colimitDecomposedCocone_ι_app_apply, key, hp, Equiv.apply_symm_apply]
    rw [hsh2]
    have := ConcreteCategory.congr_hom (hm ⟨p.1, x⟩) g
    rw [ConcreteCategory.comp_apply] at this
    exact this.trans (colimitDecomposedDescFun_ι_app G s p.1 x g).symm

/-- Objectwise: the colimit of `G : Decomposed I ⥤ Type v` is the (shrunk)
disjoint union of the colimits over each component. -/
private noncomputable def colimitDecomposedIso (G : (Decomposed I) ⥤ Type v) :
    colimit G ≅ Shrink.{v} (Σ c, colimit (Sigma.incl c ⋙ G)) :=
  (colimit.isColimit G).coconePointUniqueUpToIso (isColimitColimitDecomposedCocone G)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the sigma-decomposition descent maps in the functor `G`. -/
private theorem colimitDecomposedDesc_naturality (G G' : (Decomposed I) ⥤ Type v) (η : G ⟶ G') :
    colim.map η ≫ colimit.desc G' (colimitDecomposedCocone G')
      = colimit.desc G (colimitDecomposedCocone G) ≫
        ↾(fun s : Shrink.{v} (Σ c, colimit (Sigma.incl c ⋙ G)) =>
          let p := (equivShrink _).symm s
          equivShrink (Σ c, colimit (Sigma.incl c ⋙ G'))
            (⟨p.1, colim.map (Functor.whiskerLeft (Sigma.incl p.1) η) p.2⟩ :
              Σ c, colimit (Sigma.incl c ⋙ G'))) := by
  refine colimit.hom_ext fun ⟨b, x⟩ => ?_
  apply ConcreteCategory.hom_ext
  intro g
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  have hLm := ConcreteCategory.congr_hom (colimit.ι_map η ⟨b,x⟩) g
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hLm
  have hWm := ConcreteCategory.congr_hom (colimit.ι_map (Functor.whiskerLeft (Sigma.incl b) η) x)
    (g : (Sigma.incl b ⋙ G).obj x)
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, Functor.whiskerLeft_app] at hWm
  refine Eq.trans (congrArg (ConcreteCategory.hom
    (colimit.desc G' (colimitDecomposedCocone G'))) hLm) ?_
  refine Eq.trans (colimit.ι_desc_apply (colimitDecomposedCocone G') ⟨b,x⟩
    ((ConcreteCategory.hom (η.app ⟨b,x⟩)) g)) ?_
  refine Eq.trans ?_
    (congrArg _ (colimit.ι_desc_apply (colimitDecomposedCocone G) ⟨b,x⟩ g)).symm
  show equivShrink _
      (⟨b, colimit.ι (Sigma.incl b ⋙ G') x ((ConcreteCategory.hom (η.app ⟨b,x⟩)) g)⟩
      : Σ c, colimit (Sigma.incl c ⋙ G'))
    = equivShrink _ (⟨((equivShrink (Σ c, colimit (Sigma.incl c ⋙ G))).symm
          (equivShrink _ (⟨b, colimit.ι (Sigma.incl b ⋙ G) x g⟩ :
            Σ c, colimit (Sigma.incl c ⋙ G)))).1,
        colim.map (Functor.whiskerLeft (Sigma.incl _) η)
          ((equivShrink (Σ c, colimit (Sigma.incl c ⋙ G))).symm
            (equivShrink _ (⟨b, colimit.ι (Sigma.incl b ⋙ G) x g⟩ :
              Σ c, colimit (Sigma.incl c ⋙ G)))).2⟩
      : Σ c, colimit (Sigma.incl c ⋙ G'))
  rw [Equiv.symm_apply_apply]
  dsimp only
  refine congrArg (equivShrink _) (Sigma.ext rfl ?_)
  simp only [heq_eq_eq]
  exact hWm.symm

/-- The colimit over `I` agrees with the colimit over the decomposed category `Decomposed I`. -/
private noncomputable def colimIsoDecomposedColim :
    (colim : (I ⥤ Type v) ⥤ Type v) ≅
      (Functor.whiskeringLeft (Decomposed I) I (Type v)).obj (decomposedTo I) ⋙ colim :=
  NatIso.ofComponents
    (fun F => (Functor.Final.colimitIso (decomposedTo I) F).symm)
    (by
      intro F F' η
      dsimp only [Functor.comp_map, Functor.whiskeringLeft_obj_map]
      rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      rw [Functor.Final.colimitIso_hom, Functor.Final.colimitIso_hom]
      exact colimit.pre_map η (decomposedTo I))

/-- The colimit over the decomposed category is `componentColimFunctor ⋙ sigmaTypeFunctor`. -/
private noncomputable def decomposedColimIsoComponentSigma :
    (Functor.whiskeringLeft (Decomposed I) I (Type v)).obj (decomposedTo I) ⋙ colim
      ≅ componentColimFunctor (I := I) ⋙ sigmaTypeFunctor :=
  NatIso.ofComponents
    (fun F => colimitDecomposedIso (decomposedTo I ⋙ F))
    (by
      intro F F' η
      dsimp only [Functor.comp_map, Functor.whiskeringLeft_obj_map]
      change colim.map (Functor.whiskerLeft (decomposedTo I) η) ≫
          colimit.desc (decomposedTo I ⋙ F')
            (colimitDecomposedCocone (decomposedTo I ⋙ F'))
        = colimit.desc (decomposedTo I ⋙ F)
            (colimitDecomposedCocone (decomposedTo I ⋙ F)) ≫
          sigmaTypeFunctor.map (componentColimFunctor.map η)
      exact colimitDecomposedDesc_naturality (decomposedTo I ⋙ F) (decomposedTo I ⋙ F')
        (Functor.whiskerLeft (decomposedTo I) η))

/-- A colimit in `Type v` is the disjoint union of the colimits over the connected components:
`colim ≅ componentColimFunctor ⋙ sigmaTypeFunctor`. -/
private noncomputable def colimIsoComponentSigma :
    (colim : (I ⥤ Type v) ⥤ Type v) ≅ componentColimFunctor ⋙ sigmaTypeFunctor :=
  colimIsoDecomposedColim ≪≫ decomposedColimIsoComponentSigma

/-- If every connected component of `I` is filtered, `componentColimFunctor` preserves finite
limits. -/
lemma componentColimFunctor_preservesLimitsOfShape
    (h : ∀ c : ConnectedComponents I, IsFiltered (ConnectedComponents.Component c))
    (L : Type w) [SmallCategory L] [FinCategory L] :
    PreservesLimitsOfShape L (componentColimFunctor (I := I)) := by
  let E := piEquivalenceFunctorDiscrete (ConnectedComponents I) (Type v)
  have hcomp : PreservesLimitsOfShape L (componentColimFunctor (I := I) ⋙ E.functor) := by
    apply preservesLimitsOfShape_of_evaluation
    rintro ⟨c⟩
    have : IsFiltered (ConnectedComponents.Component c) := h c
    have : PreservesFiniteLimits
        (colim : (ConnectedComponents.Component c ⥤ Type v) ⥤ Type v) :=
      filtered_colim_preservesFiniteLimits_of_types
    show PreservesLimitsOfShape L
      (((Functor.whiskeringLeft (ConnectedComponents.Component c) I (Type v)).obj c.ι) ⋙ colim)
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves _ E.functor

/-- Evaluation at an index preserves limits of shape `L` in a product of copies of `Type v`. -/
lemma preservesLimitsOfShape_piEval (ι : Type*) (L : Type w) [SmallCategory L] [Small.{v} L]
    (c : ι) : PreservesLimitsOfShape L (Pi.eval (fun _ : ι => Type v) c) :=
  preservesLimitsOfShape_of_natIso (piEquivalenceFunctorDiscreteCompEvaluationIso (Type v) c)

/-- A compatible family for `K ⋙ sigmaTypeFunctor` over a connected shape has a constant index
coordinate `c₀`, and its second coordinates form a compatible family for `K` at `c₀`. -/
private lemma exists_sections_of_sigmaTypeFunctor_sections {L : Type w} [SmallCategory L]
    [IsConnected L] (K : L ⥤ (ConnectedComponents I → Type v))
    (s : ∀ j, (K ⋙ sigmaTypeFunctor).obj j) (hs : s ∈ (K ⋙ sigmaTypeFunctor).sections) :
    ∃ (c₀ : ConnectedComponents I) (t : ∀ j, K.obj j c₀),
      t ∈ (K ⋙ Pi.eval (fun _ : ConnectedComponents I => Type v) c₀).sections ∧
        ∀ j, equivShrink (Σ c, K.obj j c) ⟨c₀, t j⟩ = s j := by
  set σ : (j : L) → (Σ c, K.obj j c) := fun j => (equivShrink (Σ c, K.obj j c)).symm (s j) with hσ
  have hcompat : ∀ {j j' : L} (f : j ⟶ j'),
      (⟨(σ j).1, (K.map f (σ j).1) (σ j).2⟩ : Σ c, K.obj j' c) = σ j' := by
    intro j j' f
    have h := hs f
    simp only [Functor.comp_map, sigmaTypeFunctor, TypeCat.ofHom_apply] at h
    simpa only [hσ, Equiv.symm_apply_apply] using congrArg (equivShrink (Σ c, K.obj j' c)).symm h
  obtain ⟨l₀⟩ := (inferInstance : Nonempty L)
  obtain ⟨c₀, hconst⟩ : ∃ c₀, ∀ j : L, (σ j).1 = c₀ :=
    ⟨(σ l₀).1, fun j => constant_of_preserves_morphisms (fun j => (σ j).1)
      (fun _ _ f => (congrArg Sigma.fst (hcompat f)).symm ▸ rfl) j l₀⟩
  have htσ : ∀ j : L, (⟨c₀, hconst j ▸ (σ j).2⟩ : Σ c, K.obj j c) = σ j :=
    fun j => Sigma.mk_eqRec (hconst j) (σ j).2
  refine ⟨c₀, fun j => hconst j ▸ (σ j).2, ?_, fun j => ?_⟩
  · intro j j' f
    simp only [Functor.comp_map, Pi.eval_map]
    exact Sigma.eq_of_mk_map_eq (fun c => ConcreteCategory.hom ((K.map f) c)) (hconst j) (σ j).2
      ((hcompat f).trans (htσ j').symm)
  · rw [htσ j, hσ]
    simp

/-- `sigmaTypeFunctor` preserves limits of every finite connected shape. -/
instance sigmaTypeFunctor_preservesLimitsOfShape
    (L : Type w) [SmallCategory L] [FinCategory L] [IsConnected L] :
    PreservesLimitsOfShape L (sigmaTypeFunctor (I := I)) := by
  have : Small.{v} L := small_map (Fintype.equivFin L)
  have hasLim : HasLimitsOfShape L (ConnectedComponents I → Type v) :=
    Adjunction.hasLimitsOfShape_of_equivalence
      (piEquivalenceFunctorDiscrete (ConnectedComponents I) (Type v)).functor
  have evalPres : ∀ c : ConnectedComponents I,
      PreservesLimitsOfShape L (Pi.eval (fun _ : ConnectedComponents I => Type v) c) :=
    preservesLimitsOfShape_piEval (ConnectedComponents I) L
  obtain ⟨l₀⟩ := (inferInstance : Nonempty L)
  constructor
  intro K
  apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
  apply Nonempty.some
  rw [Types.isLimit_iff]
  intro s hs
  obtain ⟨c₀, t, ht, hts⟩ := exists_sections_of_sigmaTypeFunctor_sections K s hs
  obtain ⟨y, hy, yuniq⟩ := (Types.isLimit_iff _).mp
    ⟨isLimitOfPreserves (Pi.eval (fun _ : ConnectedComponents I => Type v) c₀)
      (limit.isLimit K)⟩ t ht
  set eL := equivShrink (Σ c, (limit.cone K).pt c) with heL
  refine ⟨eL ⟨c₀, y⟩, fun j => ?_, fun x' hx' => ?_⟩
  · simp only [Functor.mapCone_π_app, sigmaTypeFunctor, TypeCat.ofHom_apply]
    rw [heL, Equiv.symm_apply_apply]
    dsimp only
    have hpy : (ConcreteCategory.hom ((limit.cone K).π.app j c₀)) y = t j := hy j
    exact (congrArg (equivShrink (Σ c, K.obj j c))
      (congrArg (fun x : K.obj j c₀ => (⟨c₀, x⟩ : Σ c, K.obj j c)) hpy)).trans (hts j)
  · set q := eL.symm x' with hq
    have hx2 : ∀ j : L, (⟨q.1, (ConcreteCategory.hom ((limit.cone K).π.app j q.1)) q.2⟩
        : Σ c, K.obj j c) = ⟨c₀, t j⟩ := by
      intro j
      have h := hx' j
      simp only [Functor.mapCone_π_app, sigmaTypeFunctor, TypeCat.ofHom_apply] at h
      rw [← heL, ← hq] at h
      exact (equivShrink (Σ c, K.obj j c)).injective (h.trans (hts j).symm)
    have hq1 : q.1 = c₀ := by simpa using congrArg Sigma.fst (hx2 l₀)
    have hy' : (hq1 ▸ q.2 : limit K c₀) = y := yuniq _ fun j =>
      Sigma.eq_of_mk_map_eq (fun c => ConcreteCategory.hom ((limit.cone K).π.app j c)) hq1 q.2
        (hx2 j)
    have hq_eq : q = ⟨c₀, y⟩ := by
      rw [← hy', Sigma.mk_eqRec hq1 q.2]
    rw [← hq_eq, hq]
    exact (eL.apply_symm_apply x').symm

/-- If every connected component of `I` is filtered, `colim : (I ⥤ Type v) ⥤ Type v` preserves
limits of every finite connected shape. -/
private theorem preservesLimitsOfShape_colim_of_isFiltered_components
    (h : ∀ c : ConnectedComponents I, IsFiltered (ConnectedComponents.Component c))
    (L : Type w) [SmallCategory L] [FinCategory L] [IsConnected L] :
    PreservesLimitsOfShape L (colim : (I ⥤ Type v) ⥤ Type v) := by
  have := componentColimFunctor_preservesLimitsOfShape h L
  exact preservesLimitsOfShape_of_natIso (colimIsoComponentSigma (I := I)).symm

end Decomposition

/-- A category `I` is **almost directed** when every connected component of `I` is a filtered
category. -/
class IsAlmostDirected (I : Type u) [Category.{v'} I] : Prop where
  /-- Every connected component of `I` is filtered. -/
  isFiltered_component : ∀ (c : ConnectedComponents I),
    IsFiltered (ConnectedComponents.Component c)

/-- For an almost-directed index category `I` and every finite connected shape `L`, the colimit
functor `colim : (I ⥤ Type v) ⥤ Type v` commutes with `L`-shaped limits. -/
@[stacks 002Y, sga "4 I 2.8" "finite connected limits"]
theorem preservesLimitsOfShape_colim_of_isConnected (I : Type u) [Category.{v'} I] [Small.{v} I]
    [IsAlmostDirected.{v'} I] (L : Type w) [SmallCategory L] [FinCategory L] [IsConnected L] :
    PreservesLimitsOfShape L (colim : (I ⥤ Type v) ⥤ Type v) :=
  preservesLimitsOfShape_colim_of_isFiltered_components (I := I)
    IsAlmostDirected.isFiltered_component L

/-- Colimits over an almost-directed index category commute with fibre products of sets. -/
@[stacks 002Y, sga "4 I 2.8" "fibre products only"]
theorem preservesLimitsOfShape_walkingCospan_colim (I : Type u) [Category.{v'} I] [Small.{v} I]
    [IsAlmostDirected.{v'} I] :
    PreservesLimitsOfShape WalkingCospan (colim : (I ⥤ Type v) ⥤ Type v) :=
  preservesLimitsOfShape_colim_of_isConnected I WalkingCospan

/-- Colimits over an almost-directed index category commute with equalizers of sets. -/
@[stacks 002Y, sga "4 I 2.8" "equalizers only"]
theorem preservesLimitsOfShape_walkingParallelPair_colim (I : Type u) [Category.{v'} I]
    [Small.{v} I] [IsAlmostDirected.{v'} I] :
    PreservesLimitsOfShape WalkingParallelPair (colim : (I ⥤ Type v) ⥤ Type v) :=
  preservesLimitsOfShape_colim_of_isConnected I WalkingParallelPair

end CategoryTheory.Limits
