module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitDirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimitAdjointForm

/-!
# The diagram `i ↦ f_i^{-1}f_{i,*}𝓕` and its cocone of counits

Let `I` be a preordered set, let `D : Iᵒᵖ ⥤ Scheme` be an inverse system of schemes with a cone
`c`, write `X = c.pt` and `f_i : X ⟶ X_i` for the projections, and let `𝓕` be a sheaf on the small
étale site of `X` with values in an arbitrary category `A`. Part (1) of [Stacks, Tag 0EYN],
`Stacks.EtaleCohomology.directImageSystem`, makes `(f_{i,*}𝓕, φ_{i'i})` a system of sheaves on
`(X_i, f_{i'i})` in the sense of [Stacks, Tag 0EZL]. Part (2) asserts
`𝓕 = colim_i f_i^{-1}f_{i,*}𝓕`, the colimit being taken over the diagram whose transition maps are

`f_{i'}^{-1}φ_{i'i} : f_i^{-1}f_{i,*}𝓕 ≅ f_{i'}^{-1}f_{i'i}^{-1}f_{i,*}𝓕 ⟶ f_{i'}^{-1}f_{i',*}𝓕`,

and the map `colim_i f_i^{-1}f_{i,*}𝓕 ⟶ 𝓕` being induced by the counits of the adjunctions
`f_i^{-1} ⊣ f_{i,*}`. This file builds that diagram as a functor `I ⥤ Sheaf`, the counits as a
cocone over it, and reduces the colimit assertion to a statement about direct images alone.

## Main definitions

* `Stacks.EtaleCohomology.coneSheafPullbackComp` — the comparison
  `f_{i'}^{-1} ∘ f_{i'i}^{-1} ≅ f_i^{-1}` adjoint to `Stacks.EtaleCohomology.coneDirectImageComp`.
* `Stacks.EtaleCohomology.coneDirectImageTransport` — a map `f_{i',*}𝓕 ⟶ f_{i',*}𝒢` read at the
  index `i` through the identifications `f_{i,*} ≅ f_{i'i,*}f_{i',*}`.
* `Stacks.EtaleCohomology.pullbackDirectImageMap` — the transition map
  `f_i^{-1}f_{i,*}𝓕 ⟶ f_{i'}^{-1}f_{i',*}𝓕` built from the map `φ_{i'i}` of
  `Stacks.EtaleCohomology.directImageSystem`.
* `Stacks.EtaleCohomology.pullbackDirectImageDiagram` — **the diagram
  `i ↦ f_i^{-1}f_{i,*}𝓕`**, a functor on `I`.
* `Stacks.EtaleCohomology.pullbackDirectImageCocone` — the cocone of counits over it, with vertex
  `𝓕`.
* `Stacks.EtaleCohomology.isColimitPullbackDirectImageCocone_of_descent` — the cocone is a colimit
  as soon as every compatible family of maps of direct images comes from a unique map of sheaves.

## Main results

* `Stacks.EtaleCohomology.homEquiv_pullbackDirectImageMap_comp` — **the transition map, read
  through the adjunction**: precomposing with it is transport along the identifications of
  direct images.
* `Stacks.EtaleCohomology.pullbackDirectImageMap_id` and
  `Stacks.EtaleCohomology.pullbackDirectImageMap_comp` — the identity and composition laws, which
  make the diagram a functor.
* `Stacks.EtaleCohomology.pullbackDirectImageMap_comp_counit` — the counits form a cocone.

## Implementation notes

**Why the diagram is a functor.** [Stacks, Tag 0EZL], and with it
`Stacks.EtaleCohomology.EtaleSheafSystem`, imposes only the cocycle condition and not an identity
law, so an arbitrary system of sheaves gives no functor on `I`. For the system of direct images
both laws hold. Every statement about the transition maps is transposed across the adjunction
`f_{i'}^{-1} ⊣ f_{i',*}`, where it becomes a statement about
`Stacks.EtaleCohomology.coneDirectImageTransport`
(`Stacks.EtaleCohomology.homEquiv_pullbackDirectImageMap_comp`, whose content is the hexagon
`Stacks.EtaleCohomology.leftAdjointCompIso_inv_homEquiv_symm`). The transport is the identity at
an identity index by the unit law `Stacks.EtaleCohomology.coneDirectImageComp_id`, and is
multiplicative by the associativity pentagon
`Stacks.EtaleCohomology.smallEtalePushforwardComp'_inv_app_cocycle`, which is also what proves the
cocycle condition of `Stacks.EtaleCohomology.directImageSystem`.

The coefficient category is arbitrary; the inverse images exist as soon as the direct images
have left adjoints, which is the hypothesis carried here, as in
`Stacks.EtaleCohomology.directImageSystem`.

## References

* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

universe w' w v u

namespace Stacks.EtaleCohomology

open LimitDirectImage (etalePullback etaleAdjunction)

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (A : Type w) [Category.{w'} A]
  (c : Cone D)

/-! ### Transport of maps of direct images along the identifications -/

section Transport

/-- **A map of direct images at the index `i'`, read at the index `i ≤ i'`.** For `a : i' ⟶ i` in
`Iᵒᵖ` and `σ : f_{i',*}𝓕 ⟶ f_{i',*}𝒢`, this is `f_{i'i,*}σ` read through the identifications
`f_{i,*} ≅ f_{i'i,*}f_{i',*}` of `Stacks.EtaleCohomology.coneDirectImageComp`. -/
def coneDirectImageTransport {i j : Iᵒᵖ} (a : i ⟶ j) {F G : Sheaf (smallEtaleTopology c.pt) A}
    (σ : (smallEtalePushforward (c.π.app i) A).obj F ⟶
      (smallEtalePushforward (c.π.app i) A).obj G) :
    (smallEtalePushforward (c.π.app j) A).obj F ⟶ (smallEtalePushforward (c.π.app j) A).obj G :=
  (coneDirectImageComp D A c a).inv.app F ≫ (systemPushforward D A a).map σ ≫
    (coneDirectImageComp D A c a).hom.app G

variable {D A c}

/-- Transport along an identity index is the identity: the unit law
`Stacks.EtaleCohomology.coneDirectImageComp_id`. -/
theorem coneDirectImageTransport_id (i : Iᵒᵖ) {F G : Sheaf (smallEtaleTopology c.pt) A}
    (σ : (smallEtalePushforward (c.π.app i) A).obj F ⟶
      (smallEtalePushforward (c.π.app i) A).obj G) :
    coneDirectImageTransport D A c (𝟙 i) σ = σ := by
  have e := coneDirectImageComp_id D A c i
  have h₁ : (coneDirectImageComp D A c (𝟙 i)).inv.app F =
      (systemPushforwardId D A i).inv.app ((smallEtalePushforward (c.π.app i) A).obj F) := by
    rw [e]
    exact Category.id_comp _
  have h₂ : (coneDirectImageComp D A c (𝟙 i)).hom.app G =
      (systemPushforwardId D A i).hom.app ((smallEtalePushforward (c.π.app i) A).obj G) := by
    rw [e]
    exact Category.comp_id _
  rw [coneDirectImageTransport, h₁, h₂]
  exact NatIso.naturality_1 (systemPushforwardId D A i) σ

/-- Transport of an identity is an identity. -/
theorem coneDirectImageTransport_one {i j : Iᵒᵖ} (a : i ⟶ j)
    (F : Sheaf (smallEtaleTopology c.pt) A) :
    coneDirectImageTransport D A c a (𝟙 ((smallEtalePushforward (c.π.app i) A).obj F)) = 𝟙 _ := by
  rw [coneDirectImageTransport, CategoryTheory.Functor.map_id]
  exact (congrArg ((coneDirectImageComp D A c a).inv.app F ≫ ·) (Category.id_comp _)).trans
    ((coneDirectImageComp D A c a).inv_hom_id_app F)

/-- **The pentagon, read on inverses.** The comparison along a composite of transitions,
followed by the comparison for the composite, is the composite of the two comparisons. This is
`Stacks.EtaleCohomology.smallEtalePushforwardComp'_inv_app_cocycle` at the factorisations of the
projections of the cone. -/
theorem coneDirectImageComp_inv_app_cocycle {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    (G : Sheaf (smallEtaleTopology c.pt) A) :
    (coneDirectImageComp D A c b).inv.app G ≫
        (systemPushforward D A b).map ((coneDirectImageComp D A c a).inv.app G) =
      (coneDirectImageComp D A c (a ≫ b)).inv.app G ≫
        (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)
          A).inv.app ((smallEtalePushforward (c.π.app i) A).obj G) :=
  smallEtalePushforwardComp'_inv_app_cocycle (c.π.app i) (D.map a) (D.map b)
    (c.π.app j) (c.w a).symm (D.map (a ≫ b)) (D.map_comp a b) (c.π.app k) (c.w b).symm
    (c.w (a ≫ b)).symm A G

/-- **The pentagon, read on homomorphisms**:
`Stacks.EtaleCohomology.coneDirectImageComp_inv_app_cocycle` with every isomorphism inverted. -/
theorem coneDirectImageComp_hom_app_cocycle {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    (G : Sheaf (smallEtaleTopology c.pt) A) :
    (systemPushforward D A b).map ((coneDirectImageComp D A c a).hom.app G) ≫
        (coneDirectImageComp D A c b).hom.app G =
      (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)
          A).hom.app ((smallEtalePushforward (c.π.app i) A).obj G) ≫
        (coneDirectImageComp D A c (a ≫ b)).hom.app G :=
  (Iso.inv_eq_inv
    ((systemPushforward D A b).mapIso ((coneDirectImageComp D A c a).app G) ≪≫
      (coneDirectImageComp D A c b).app G)
    ((smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b) A).app
        ((smallEtalePushforward (c.π.app i) A).obj G) ≪≫
      (coneDirectImageComp D A c (a ≫ b)).app G)).mp
    (coneDirectImageComp_inv_app_cocycle a b G)

/-- **Transport is multiplicative**: transporting along a composite of transitions is transporting
along each in turn. -/
theorem coneDirectImageTransport_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    {F G : Sheaf (smallEtaleTopology c.pt) A}
    (σ : (smallEtalePushforward (c.π.app i) A).obj F ⟶
      (smallEtalePushforward (c.π.app i) A).obj G) :
    coneDirectImageTransport D A c (a ≫ b) σ =
      coneDirectImageTransport D A c b (coneDirectImageTransport D A c a σ) := by
  have hS : (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)
        A).inv.app ((smallEtalePushforward (c.π.app i) A).obj F) ≫
      (systemPushforward D A b).map ((systemPushforward D A a).map σ) ≫
        (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)
          A).hom.app ((smallEtalePushforward (c.π.app i) A).obj G) =
      (systemPushforward D A (a ≫ b)).map σ :=
    NatIso.naturality_1 (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b))
      (D.map_comp a b) A) σ
  calc coneDirectImageTransport D A c (a ≫ b) σ
      = ((coneDirectImageComp D A c (a ≫ b)).inv.app F ≫
          (smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)
            A).inv.app ((smallEtalePushforward (c.π.app i) A).obj F)) ≫
          (systemPushforward D A b).map ((systemPushforward D A a).map σ) ≫
          ((smallEtalePushforwardComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)
            A).hom.app ((smallEtalePushforward (c.π.app i) A).obj G) ≫
            (coneDirectImageComp D A c (a ≫ b)).hom.app G) := by
        rw [coneDirectImageTransport, ← hS]
        simp only [Category.assoc]
    _ = ((coneDirectImageComp D A c b).inv.app F ≫
          (systemPushforward D A b).map ((coneDirectImageComp D A c a).inv.app F)) ≫
          (systemPushforward D A b).map ((systemPushforward D A a).map σ) ≫
          ((systemPushforward D A b).map ((coneDirectImageComp D A c a).hom.app G) ≫
            (coneDirectImageComp D A c b).hom.app G) := by
        rw [coneDirectImageComp_inv_app_cocycle, coneDirectImageComp_hom_app_cocycle]
    _ = coneDirectImageTransport D A c b (coneDirectImageTransport D A c a σ) := by
        simp only [coneDirectImageTransport, CategoryTheory.Functor.map_comp, Category.assoc]

/-- Transporting the direct image of a map of sheaves gives its direct image. -/
theorem coneDirectImageTransport_map {i j : Iᵒᵖ} (a : i ⟶ j)
    {F G : Sheaf (smallEtaleTopology c.pt) A} (χ : F ⟶ G) :
    coneDirectImageTransport D A c a ((smallEtalePushforward (c.π.app i) A).map χ) =
      (smallEtalePushforward (c.π.app j) A).map χ :=
  NatIso.naturality_1 (coneDirectImageComp D A c a) χ

end Transport

/-! ### The inverse images along the projections -/

section Pullback

variable [∀ i : Iᵒᵖ, (smallEtalePushforward (c.π.app i) A).IsRightAdjoint]

variable [∀ (i j : Iᵒᵖ) (a : i ⟶ j), (systemPushforward D A a).IsRightAdjoint]

/-- The comparison `f_{i'}^{-1} ∘ f_{i'i}^{-1} ≅ f_i^{-1}` of inverse images along the
factorisation `f_i = f_{i'} ≫ f_{i'i}` of a projection: the left adjoint comparison of
`Stacks.EtaleCohomology.coneDirectImageComp`. -/
def coneSheafPullbackComp {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemPullback D A a ⋙ etalePullback (c.π.app i) A ≅ etalePullback (c.π.app j) A :=
  Adjunction.leftAdjointCompIso (systemAdjunction D A a) (etaleAdjunction (c.π.app i) A)
    (etaleAdjunction (c.π.app j) A) (coneDirectImageComp D A c a)

variable (F : Sheaf (smallEtaleTopology c.pt) A)

/-- **The transition map `f_i^{-1}f_{i,*}𝓕 ⟶ f_{i'}^{-1}f_{i',*}𝓕` of the diagram of
[Stacks, Tag 0EYN] (2)**, for `a : i' ⟶ i` in `Iᵒᵖ`: the comparison
`f_i^{-1} ≅ f_{i'}^{-1} f_{i'i}^{-1}` followed by `f_{i'}^{-1}φ_{i'i}`, where `φ_{i'i}` is the map
of the system of sheaves `Stacks.EtaleCohomology.directImageSystem` of part (1). -/
def pullbackDirectImageMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (etalePullback (c.π.app j) A).obj ((directImageSystem D A c F).obj j) ⟶
      (etalePullback (c.π.app i) A).obj ((directImageSystem D A c F).obj i) :=
  (coneSheafPullbackComp D A c a).inv.app ((directImageSystem D A c F).obj j) ≫
    (etalePullback (c.π.app i) A).map ((directImageSystem D A c F).map a)

variable {D A c F}

/-- **The transition map, read through the adjunction.** Precomposing a map
`τ : f_i^{-1}f_{i,*}𝓕 ⟶ 𝒢` with the transition map and transposing across `f_j^{-1} ⊣ f_{j,*}`
is transporting the transpose of `τ` along the identifications of direct images. -/
theorem homEquiv_pullbackDirectImageMap_comp {i j : Iᵒᵖ} (a : i ⟶ j)
    {G : Sheaf (smallEtaleTopology c.pt) A}
    (τ : (etalePullback (c.π.app i) A).obj ((directImageSystem D A c F).obj i) ⟶ G) :
    (etaleAdjunction (c.π.app j) A).homEquiv _ _
        (pullbackDirectImageMap D A c F (i := i) (j := j) a ≫ τ) =
      coneDirectImageTransport D A c a ((etaleAdjunction (c.π.app i) A).homEquiv _ _ τ) := by
  refine (Equiv.eq_symm_apply _).mp ((Category.assoc _ _ _).trans ?_)
  refine Eq.trans ?_ (leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction D A a)
    (etaleAdjunction (c.π.app i) A) (etaleAdjunction (c.π.app j) A) (coneDirectImageComp D A c a)
    ((coneDirectImageComp D A c a).inv.app F) ((etaleAdjunction (c.π.app i) A).homEquiv _ _ τ))
  exact congrArg (fun z => (coneSheafPullbackComp D A c a).inv.app
      ((directImageSystem D A c F).obj j) ≫
        (etalePullback (c.π.app i) A).map ((directImageSystem D A c F).map a) ≫ z)
    (((etaleAdjunction (c.π.app i) A).homEquiv _ _).symm_apply_apply τ).symm

/-- **The identity law**: the transition map attached to an identity index is the identity. -/
theorem pullbackDirectImageMap_id (i : Iᵒᵖ) :
    pullbackDirectImageMap D A c F (i := i) (j := i) (𝟙 i) = 𝟙 _ := by
  refine ((etaleAdjunction (c.π.app i) A).homEquiv _ _).injective ?_
  have h := homEquiv_pullbackDirectImageMap_comp (D := D) (A := A) (c := c) (F := F) (𝟙 i) (𝟙 _)
  rw [Category.comp_id, coneDirectImageTransport_id] at h
  exact h

/-- **The composition law**: the transition map attached to a composite is the composite of the
transition maps. -/
theorem pullbackDirectImageMap_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    pullbackDirectImageMap D A c F (i := i) (j := k) (a ≫ b) =
      pullbackDirectImageMap D A c F (i := j) (j := k) b ≫
        pullbackDirectImageMap D A c F (i := i) (j := j) a := by
  refine ((etaleAdjunction (c.π.app k) A).homEquiv _ _).injective ?_
  have h₁ := homEquiv_pullbackDirectImageMap_comp (D := D) (A := A) (c := c) (F := F)
    (a ≫ b) (𝟙 _)
  have h₂ := homEquiv_pullbackDirectImageMap_comp b
    (pullbackDirectImageMap D A c F (i := i) (j := j) a)
  have h₃ := homEquiv_pullbackDirectImageMap_comp (D := D) (A := A) (c := c) (F := F) a (𝟙 _)
  refine (congrArg ((etaleAdjunction (c.π.app k) A).homEquiv _ _)
    (Category.comp_id _).symm).trans (h₁.trans ?_)
  refine (coneDirectImageTransport_comp a b _).trans (Eq.trans ?_ h₂.symm)
  exact congrArg (coneDirectImageTransport D A c b)
    (h₃.symm.trans (congrArg ((etaleAdjunction (c.π.app j) A).homEquiv _ _)
      (Category.comp_id _)))

/-- **The counits form a cocone**: for `i ≤ i'` the counit at `i'` precomposed with the transition
map is the counit at `i`. -/
theorem pullbackDirectImageMap_comp_counit {i j : Iᵒᵖ} (a : i ⟶ j) :
    pullbackDirectImageMap D A c F (i := i) (j := j) a ≫
        (etaleAdjunction (c.π.app i) A).counit.app F =
      (etaleAdjunction (c.π.app j) A).counit.app F := by
  have e : ∀ k : Iᵒᵖ, (etaleAdjunction (c.π.app k) A).homEquiv _ _
      ((etaleAdjunction (c.π.app k) A).counit.app F) = 𝟙 _ := fun k =>
    (Equiv.eq_symm_apply _).mp
      ((etaleAdjunction (c.π.app k) A).homEquiv_symm_id F).symm
  refine ((etaleAdjunction (c.π.app j) A).homEquiv _ _).injective ?_
  exact (homEquiv_pullbackDirectImageMap_comp (D := D) (A := A) (c := c) a _).trans
    ((congrArg (coneDirectImageTransport D A c a) (e i)).trans
      ((coneDirectImageTransport_one a F).trans (e j).symm))

variable (D A c F)

/-- **The diagram `i ↦ f_i^{-1}f_{i,*}𝓕` of [Stacks, Tag 0EYN] (2)**, a functor on `I`: its
transition maps are `Stacks.EtaleCohomology.pullbackDirectImageMap`, built from the system of
sheaves `Stacks.EtaleCohomology.directImageSystem` of part (1). -/
def pullbackDirectImageDiagram : I ⥤ Sheaf (smallEtaleTopology c.pt) A where
  obj i := (etalePullback (c.π.app (op i)) A).obj ((directImageSystem D A c F).obj (op i))
  map {X Y} f := pullbackDirectImageMap D A c F (i := op Y) (j := op X) f.op
  map_id i := pullbackDirectImageMap_id (op i)
  map_comp f g := pullbackDirectImageMap_comp g.op f.op

/-- **The cocone of counits** over `Stacks.EtaleCohomology.pullbackDirectImageDiagram`, with
vertex `𝓕`: its leg at `i` is the counit `f_i^{-1}f_{i,*}𝓕 ⟶ 𝓕`. The map from the colimit of
the diagram to `𝓕` that it induces is the canonical map of [Stacks, Tag 0EYN] (2). -/
def pullbackDirectImageCocone : Cocone (pullbackDirectImageDiagram D A c F) where
  pt := F
  ι :=
    { app i := (etaleAdjunction (c.π.app (op i)) A).counit.app F
      naturality _ _ f := (pullbackDirectImageMap_comp_counit f.op).trans
        (Category.comp_id _).symm }

/-- **The colimit assertion of [Stacks, Tag 0EYN] (2), reduced to direct images.** If every
family of maps of direct images `σ_i : f_{i,*}𝓕 ⟶ f_{i,*}𝒢` compatible with the identifications
`f_{i,*} ≅ f_{i'i,*}f_{i',*}` is the family of direct images of a unique `χ : 𝓕 ⟶ 𝒢`, then the
cocone of counits is a colimit cocone. The proof is the adjunction: a cocone with legs `τ_i` is
the same as such a compatible family, `σ_i` being the transpose of `τ_i`. -/
def isColimitPullbackDirectImageCocone_of_descent
    (h : ∀ (G : Sheaf (smallEtaleTopology c.pt) A)
      (σ : ∀ i : Iᵒᵖ, (smallEtalePushforward (c.π.app i) A).obj F ⟶
        (smallEtalePushforward (c.π.app i) A).obj G),
      (∀ {i j : Iᵒᵖ} (a : i ⟶ j), σ j = coneDirectImageTransport D A c a (σ i)) →
        ∃! χ : F ⟶ G, ∀ i : Iᵒᵖ, (smallEtalePushforward (c.π.app i) A).map χ = σ i) :
    IsColimit (pullbackDirectImageCocone D A c F) :=
  IsColimit.ofExistsUnique fun s => by
    obtain ⟨χ, hχ, hu⟩ := h s.pt
      (fun i => (etaleAdjunction (c.π.app i) A).homEquiv _ _ (s.ι.app i.unop))
      (fun {i j} a => (congrArg ((etaleAdjunction (c.π.app j) A).homEquiv _ _)
          ((s.ι.naturality a.unop).trans (Category.comp_id _)).symm).trans
        (homEquiv_pullbackDirectImageMap_comp a (s.ι.app i.unop)))
    refine ⟨χ, fun i => ?_, fun y hy => hu y fun i => ?_⟩
    · exact (counit_comp_eq_iff (etaleAdjunction (c.π.app (op i)) A) χ (s.ι.app i)).mpr
        (hχ (op i))
    · exact (counit_comp_eq_iff (etaleAdjunction (c.π.app i) A) y (s.ι.app i.unop)).mp
        (hy i.unop)

end Pullback

end Stacks.EtaleCohomology

end
