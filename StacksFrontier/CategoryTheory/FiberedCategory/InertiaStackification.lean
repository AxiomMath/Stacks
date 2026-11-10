module

public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing
public import StacksFrontier.CategoryTheory.Sites.Stack.IsomPresheaf

/-!
# The stackification of the inertia is the inertia of the stackification

Let `(𝒞, J)` be a site and let `p : 𝒳 ⥤ 𝒞` be a fibred category over `𝒞`. Let `G : 𝒳 ⥤ 𝒳'` be the
stackification of `𝒳` (Stacks 02ZN): a 1-morphism of fibred categories over `𝒞` whose target
`p' : 𝒳' ⥤ 𝒞` is a stack, such that (1) for every `U` and every `x`, `y` in the fibre `𝒳_U` the
induced map `Mor(x, y) ⟶ Mor(G x, G y)` of presheaves on `𝒞/U` exhibits the target as the
sheafification of the source, and (2) every object of `𝒳'` is, locally on the base, in the
essential image of `G`.
Stacks 06NS says that the stackification of the inertia `I_𝒳` is the inertia `I_{𝒳'}` of the
stackification: the functoriality 1-morphism `I_G : I_𝒳 ⥤ I_{𝒳'}`, `(x, α) ↦ (G x, G α)`, is a
stackification of `I_𝒳` in exactly that sense.

The mathematics is that the inertia is a 2-fibre product of the diagonal with itself (Stacks 034H
(1)) and that stackification is compatible with 2-fibre products (Stacks 04Y1), the 2-fibre product
of stacks being a stack (Stacks 026G).

## Main results

* `CategoryTheory.RelativeInertia.isStackification_functoriality`: Stacks 06NS.

## Implementation notes

The inertia of a category over `𝒞` is the canonical `CategoryTheory.RelativeInertia` of Stacks 034I
taken at the structure functor itself — `AbsoluteInertia p = RelativeInertia p`, the case `𝒮' = 𝒞`,
`F = p`, `p' = 𝟭 𝒞` of the relative inertia — with structure functor
`CategoryTheory.RelativeInertia.toBase p = π ⋙ p`, and it is a fibred category over `𝒞` by Stacks
034H (2) (`CategoryTheory.RelativeInertia.isFibered`, applied through
`CategoryTheory.Functor.isFibredOneMorphism_id`); those instances are supplied inside the
statement from the hypotheses that provide them rather than assumed. The canonical 1-morphism
`I_G` is `CategoryTheory.RelativeInertia.functoriality`, `(x, α) ↦ (G x, G α)`, so no new functor
is introduced and the conclusion is a statement about that functor.

"`G` is a stackification" is spelled out from the two conditions of Stacks 02ZN rather than
referred to a predicate, there being none in the tree yet; the two conditions are then repeated
verbatim for `I_G` in the conclusion, so that hypothesis and conclusion assert one and the same
notion of the two 1-morphisms `G` and `I_G`.

Condition (1) is read through the canonical map of Stacks 042V,
`CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap`, between the presheaves `Mor(x, y)` of
Stacks 02ZB on the slice `𝒞/U`. "Identifies the target with the sheafification of the source" is
stated as: the target is a sheaf, and the map is locally injective and locally surjective for the
induced topology `J.over U`. That is the standard characterisation of a sheafification map
(`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`), and it is used in place of an isomorphism
from a sheafification functor because `Mor(x, y)` is valued in the hom-universe of `𝒳`, which
Mathlib's sheafification of type-valued presheaves does not accommodate. The sheaf half of the
condition is not repeated as a clause: on the hypothesis side it is `hp'.isMorSheaf` and on the
conclusion side it is the `IsStack` conjunct, so a separate clause would be redundant.

Condition (2) is read in sieve language and without chosen pullbacks: for every object `x'` there
is a covering sieve `R` of `p'.obj x'` such that for each `f : V ⟶ p'.obj x'` in `R` there is an
object `y` of `𝒳` and a morphism `G y ⟶ x'` strongly cartesian over `f`. Giving such a morphism is
the same as giving an isomorphism `f^* x' ≅ G y` in the fibre over `V`, cartesian lifts of `f` at
`x'` being unique up to unique vertical isomorphism, so this is "`x'|_V` is in the essential image
of `𝒳_V ⥤ 𝒳'_V`"; and quantifying over all objects `x'` of `𝒳'` with `U = p'.obj x'` is quantifying
over all `U` and all objects of the fibre `𝒳'_U`.

That the inertia of a stack is a stack (Stacks 036Y (1)) appears in the conclusion rather than as a
hypothesis: `I_{𝒳'}` can only be *the* stackification of `I_𝒳` if it is a stack, and the source's
route obtains this along with the rest, the 2-fibre product of stacks being a stack.

The hom-universes of `𝒳` and `𝒳'` are one and the same `v`; the hom-universe `vb` of the site and
all three object universes are independent. A natural transformation `Mor(x, y) ⟶ Mor(G x, G y)` is
a map of presheaves valued in the hom-universes of `𝒳` and of `𝒳'` respectively, so the map of
Stacks 042V exists without a universe lift only when those two agree; the inertia has the
hom-universe of the category it is formed from, so the same identification serves both
applications of the condition. Nothing ties the site to them, and the site must be left free: the
quotient stack of a groupoid in algebraic spaces has morphisms one universe above those of the big
fppf site it lies over, so a shared hom-universe would put this result out of reach of the one
application that needs it, the identification of the inertia of a quotient stack.

## References

* [StacksProject 06NS](https://stacks.math.columbia.edu/tag/06NS)
-/


@[expose] public section

open CategoryTheory

universe vb v u₁ u₂ u₃

namespace CategoryTheory

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒳 : Type u₂} [Category.{v} 𝒳]
  {𝒳' : Type u₃} [Category.{v} 𝒳']

section Helpers

-- The chosen pullbacks of `CategoryTheory.Functor.IsPreFibered` and the inclusion of a fibre are
-- semireducible, so the endpoints of the composites below agree only up to unfolding them; this is
-- the same setting the descent files reused here are elaborated in.
set_option backward.isDefEq.respectTransparency false

-- Several of the helpers below do not need every fibredness instance of the block they sit in.

namespace RelativeInertia

/-! ### Strongly cartesian morphisms of the inertia

A morphism of the absolute inertia is strongly cartesian for `toBase p` exactly when its underlying
morphism of `𝒳` is strongly cartesian for `p`. The easy direction needs no hypothesis; the converse
uses that `toBase p` is fibred, so that the given morphism differs from a lift built out of a
strongly cartesian morphism of `𝒳` by a vertical isomorphism. -/

universe u₄

variable {𝒴 : Type u₄} [Category.{v} 𝒴] {p : 𝒴 ⥤ 𝒞}

/-- An automorphism of an object of the absolute inertia lies over an identity. -/
private lemma isHomLift_auto {A : RelativeInertia p} {R : 𝒞} (hA : p.obj A.obj = R) :
    p.IsHomLift (𝟙 R) A.auto.asIso.hom :=
  IsHomLift.of_fac' p _ A.auto.asIso.hom hA hA (by rw [A.cond]; simp)

/-- The inverse of the automorphism of an object of the absolute inertia lies over an identity. -/
private lemma isHomLift_auto_inv {A : RelativeInertia p} {R : 𝒞} (hA : p.obj A.obj = R) :
    p.IsHomLift (𝟙 R) A.auto.asIso.inv :=
  IsHomLift.of_fac' p _ A.auto.asIso.inv hA hA (by rw [A.cond_inv]; simp)

/-- An endomorphism lying over an identity is sent to an identity by the structure functor. -/
private lemma map_eq_id_of_isHomLift_id (R : 𝒞) {a : 𝒴} (φ : a ⟶ a) [p.IsHomLift (𝟙 R) φ] :
    p.map φ = 𝟙 (p.obj a) := by
  obtain rfl := IsHomLift.domain_eq p (𝟙 R) φ
  exact (IsHomLift.eq_of_isHomLift p (𝟙 (p.obj a)) φ).symm

/-- A morphism of the absolute inertia whose underlying morphism of `𝒳` is strongly cartesian is
strongly cartesian for the structure functor of the inertia: a lift through it is the same thing as
a lift of the underlying morphism, and the induced morphism automatically commutes with the
automorphisms. -/
private lemma isStronglyCartesian_of_hom {A B : RelativeInertia p} {R T : 𝒞} (f : R ⟶ T)
    (ψ : A ⟶ B) (h : p.IsStronglyCartesian f ψ.hom) :
    (RelativeInertia.toBase p).IsStronglyCartesian f ψ := by
  have := h
  have hAR : p.obj A.obj = R := IsHomLift.domain_eq p f ψ.hom
  have hA := isHomLift_auto hAR
  have hlift : (RelativeInertia.toBase p).IsHomLift f ψ :=
    (RelativeInertia.isHomLift_π_comp_iff f ψ).mpr inferInstance
  apply Functor.IsStronglyCartesian.mk
  intro Z g χ hχ
  have := hχ
  have hZ := isHomLift_auto (rfl : p.obj Z.obj = p.obj Z.obj)
  have hχ' : p.IsHomLift (g ≫ f) χ.hom :=
    (RelativeInertia.isHomLift_π_comp_iff (g ≫ f) χ).mp hχ
  set χ₀ : Z.obj ⟶ A.obj :=
    Functor.IsStronglyCartesian.map p f ψ.hom (rfl : g ≫ f = g ≫ f) χ.hom with hχ₀
  have hχ₀lift : p.IsHomLift g χ₀ :=
    Functor.IsStronglyCartesian.map_isHomLift p f ψ.hom rfl χ.hom
  have hχ₀fac : χ₀ ≫ ψ.hom = χ.hom :=
    Functor.IsStronglyCartesian.fac p f ψ.hom rfl χ.hom
  have hcomm : χ₀ ≫ A.auto.asIso.hom = Z.auto.asIso.hom ≫ χ₀ := by
    have h₁ : p.IsHomLift g (χ₀ ≫ A.auto.asIso.hom) := inferInstance
    have h₂ : p.IsHomLift g (Z.auto.asIso.hom ≫ χ₀) := by
      simpa using (inferInstance : p.IsHomLift (𝟙 (p.obj Z.obj) ≫ g) (Z.auto.asIso.hom ≫ χ₀))
    refine Functor.IsStronglyCartesian.ext p f ψ.hom g ?_
    rw [Category.assoc, ← ψ.comm, ← Category.assoc, hχ₀fac, Category.assoc, hχ₀fac]
    exact χ.comm
  refine ⟨⟨χ₀, hcomm⟩, ⟨(RelativeInertia.isHomLift_π_comp_iff g _).mpr hχ₀lift,
    RelativeInertiaHom.ext hχ₀fac⟩, ?_⟩
  rintro τ ⟨hτlift, hτfac⟩
  refine RelativeInertiaHom.ext ?_
  have : p.IsHomLift g τ.hom := (RelativeInertia.isHomLift_π_comp_iff g τ).mp hτlift
  refine Functor.IsStronglyCartesian.map_uniq p f ψ.hom (rfl : g ≫ f = g ≫ f) χ.hom τ.hom ?_
  have h : (τ ≫ ψ).hom = χ.hom := by rw [hτfac]
  simpa using h

/-- A strongly cartesian lift in `𝒳` of `f` at the underlying object of an object `B` of the
absolute inertia carries an automorphism compatible with `B`'s, induced by the universal property
of the lift. -/
private lemma exists_auto_of_isStronglyCartesian (B : RelativeInertia p) {R T : 𝒞} (f : R ⟶ T)
    {x : 𝒴} (φ : x ⟶ B.obj) (hφ : p.IsStronglyCartesian f φ) :
    ∃ β : x ≅ x, p.IsHomLift (𝟙 R) β.hom ∧ β.hom ≫ φ = φ ≫ B.auto.asIso.hom := by
  have := hφ
  have hBT : p.obj B.obj = T := IsHomLift.codomain_eq p f φ
  have := isHomLift_auto hBT
  have := isHomLift_auto_inv hBT
  have hf : f = 𝟙 R ≫ f := (Category.id_comp f).symm
  have : p.IsHomLift (𝟙 R) (𝟙 x) := IsHomLift.id (IsHomLift.domain_eq p f φ)
  have hmk : ∀ c : B.obj ⟶ B.obj, p.IsHomLift (𝟙 T) c →
      ∃ α : x ⟶ x, p.IsHomLift (𝟙 R) α ∧ α ≫ φ = φ ≫ c := fun c _ ↦
    ⟨_, Functor.IsStronglyCartesian.map_isHomLift p f φ hf (φ ≫ c),
      Functor.IsStronglyCartesian.fac p f φ hf _⟩
  have hinv : ∀ (a b : x ⟶ x) (c d : B.obj ⟶ B.obj) [p.IsHomLift (𝟙 R) a] [p.IsHomLift (𝟙 R) b],
      a ≫ φ = φ ≫ c → b ≫ φ = φ ≫ d → c ≫ d = 𝟙 _ → a ≫ b = 𝟙 x := by
    intro a b c d _ _ ha hb hcd
    refine Functor.IsStronglyCartesian.ext p f φ (𝟙 R) ?_
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, hcd, Category.comp_id,
      Category.id_comp]
  obtain ⟨αh, hαhlift, hαhfac⟩ := hmk B.auto.asIso.hom inferInstance
  obtain ⟨αi, hαilift, hαifac⟩ := hmk B.auto.asIso.inv inferInstance
  exact ⟨⟨αh, αi, hinv _ _ _ _ hαhfac hαifac B.auto.asIso.hom_inv_id,
    hinv _ _ _ _ hαifac hαhfac B.auto.asIso.inv_hom_id⟩, hαhlift, hαhfac⟩

/-- The object of the absolute inertia produced by `exists_auto_of_isStronglyCartesian`, together
with the morphism of the inertia the cartesian lift becomes. -/
private lemma exists_lift_of_isStronglyCartesian (B : RelativeInertia p) {R T : 𝒞} (f : R ⟶ T)
    {x : 𝒴} (φ : x ⟶ B.obj) (hφ : p.IsStronglyCartesian f φ) :
    ∃ (A : RelativeInertia p) (ψ : A ⟶ B), p.IsStronglyCartesian f ψ.hom := by
  obtain ⟨β, hβlift, hβfac⟩ := exists_auto_of_isStronglyCartesian B f φ hφ
  have := hβlift
  exact ⟨⟨x, Aut.of β, map_eq_id_of_isHomLift_id (p := p) R β.hom⟩, ⟨φ, hβfac.symm⟩, hφ⟩

/-- Conversely, a strongly cartesian morphism of the absolute inertia has strongly cartesian
underlying morphism. Two strongly cartesian lifts of one and the same morphism at one and the same
object differ by a vertical isomorphism, and one such lift is built from a strongly cartesian
morphism of `𝒳` by `exists_lift_of_isStronglyCartesian`. -/
private lemma isStronglyCartesian_hom [p.IsFibered] {A B : RelativeInertia p} {R T : 𝒞} (f : R ⟶ T)
    (ψ : A ⟶ B) (h : (RelativeInertia.toBase p).IsStronglyCartesian f ψ) :
    p.IsStronglyCartesian f ψ.hom := by
  have := h
  have hBT : p.obj B.obj = T := IsHomLift.codomain_eq (RelativeInertia.toBase p) f ψ
  obtain ⟨x, φ, hφc⟩ := IsPreFibered.exists_isCartesian p hBT f
  have : p.IsCartesian f φ := hφc
  have hφ : p.IsStronglyCartesian f φ := inferInstance
  obtain ⟨A₀, ψ₀, hψ₀⟩ := exists_lift_of_isStronglyCartesian B f φ hφ
  have hψ₀c : (RelativeInertia.toBase p).IsStronglyCartesian f ψ₀ :=
    isStronglyCartesian_of_hom f ψ₀ hψ₀
  have := hψ₀
  set θ : A ≅ A₀ := Functor.IsCartesian.domainUniqueUpToIso (RelativeInertia.toBase p) f ψ₀ ψ
    with hθ
  have hθfac : θ.hom ≫ ψ₀ = ψ := by
    rw [hθ, Functor.IsCartesian.domainUniqueUpToIso_hom]
    exact Functor.IsCartesian.fac (RelativeInertia.toBase p) f ψ₀ ψ
  have hθlift : p.IsHomLift (𝟙 R) θ.hom.hom :=
    (RelativeInertia.isHomLift_π_comp_iff (𝟙 R) θ.hom).mp inferInstance
  have hθiso : IsIso θ.hom.hom := by
    have h0 : IsIso ((RelativeInertia.π p).map θ.hom) := inferInstance
    exact h0
  have hcart : p.IsStronglyCartesian (𝟙 R ≫ f) (θ.hom.hom ≫ ψ₀.hom) := inferInstance
  have hgoal : θ.hom.hom ≫ ψ₀.hom = ψ.hom := congrArg RelativeInertiaHom.hom hθfac
  rwa [Category.id_comp, hgoal] at hcart

/-! ### `π` and `I_G` as 1-morphisms of fibred categories over `𝒞` -/

/-- The forgetful functor `π : I_𝒴 ⥤ 𝒴` is a 1-morphism of fibred categories over `𝒞`. -/
private lemma isFibredOneMorphism_π (p : 𝒴 ⥤ 𝒞) [p.IsFibered] :
    (RelativeInertia.toBase p).IsFibredOneMorphism p (RelativeInertia.π p) where
  comp_eq := rfl
  map_isStronglyCartesian := by
    intro _ _ f _ _ ψ h
    exact isStronglyCartesian_hom f ψ h

/-- **Stacks 04Z4 as a 1-morphism of fibred categories.** The functoriality functor `I_G` of a
1-morphism `G` of fibred categories over `𝒞` is again a 1-morphism of fibred categories over `𝒞`:
it is strictly over `𝒞` by `RelativeInertia.functoriality_comp_toBase`, and it preserves strongly
cartesian morphisms because a morphism of the inertia is strongly cartesian exactly when its
underlying morphism is. -/
private lemma isFibredOneMorphism_functoriality {p : 𝒳 ⥤ 𝒞} {p' : 𝒳' ⥤ 𝒞} {G : 𝒳 ⥤ 𝒳'}
    [p.IsFibered] [p'.IsFibered] (hG : p.IsFibredOneMorphism p' G) :
    (RelativeInertia.toBase p).IsFibredOneMorphism (RelativeInertia.toBase p')
      (RelativeInertia.functoriality p p' G hG.comp_eq) where
  comp_eq := RelativeInertia.functoriality_comp_toBase p p' G hG.comp_eq
  map_isStronglyCartesian := by
    intro _ _ f _ _ ψ h
    exact isStronglyCartesian_of_hom f _
      (hG.map_isStronglyCartesian f ψ.hom (isStronglyCartesian_hom f ψ h))

/-! ### The automorphism attached to an object of a fibre of the inertia -/

variable [p.IsFibered]

/-- The functor `I_𝒴_U ⥤ 𝒴_U` induced by `π` on the fibres over `U`. -/
private abbrev fiberπ (U : 𝒞) : (RelativeInertia.toBase p).Fiber U ⥤ p.Fiber U :=
  Functor.fiberFunctorOfCompEq (isFibredOneMorphism_π p).comp_eq U

/-- The automorphism of an object `A` of the fibre of the inertia over `U`, read as an endomorphism
of the underlying object in the fibre of `p` over `U`. -/
private def autoHom {U : 𝒞} (A : (RelativeInertia.toBase p).Fiber U) :
    (fiberπ (p := p) U).obj A ⟶ (fiberπ (p := p) U).obj A :=
  ⟨A.1.auto.asIso.hom, isHomLift_auto (p := p) A.2⟩

/-- The automorphism of `A`, read as an endomorphism of `A` in the fibre of the inertia over
`U`. -/
private def fiberAuto {U : 𝒞} (A : (RelativeInertia.toBase p).Fiber U) : A ⟶ A :=
  ⟨⟨A.1.auto.asIso.hom, rfl⟩,
    (RelativeInertia.isHomLift_π_comp_iff (p := p) (𝟙 U) _).mpr (isHomLift_auto (p := p) A.2)⟩

/-- The automorphism of `A`, read as an automorphism of the underlying object in the fibre of `p`
over `U`. -/
private def autoIso {U : 𝒞} (A : (RelativeInertia.toBase p).Fiber U) :
    (fiberπ (p := p) U).obj A ≅ (fiberπ (p := p) U).obj A where
  hom := autoHom (p := p) A
  inv := ⟨A.1.auto.asIso.inv, isHomLift_auto_inv (p := p) A.2⟩
  hom_inv_id := Functor.Fiber.hom_ext A.1.auto.asIso.hom_inv_id
  inv_hom_id := Functor.Fiber.hom_ext A.1.auto.asIso.inv_hom_id

@[simp]
private lemma autoIso_hom {U : 𝒞} (A : (RelativeInertia.toBase p).Fiber U) :
    (autoIso (p := p) A).hom = autoHom (p := p) A := rfl

@[simp]
private lemma fiberInclusion_map_autoHom {U : 𝒞} (A : (RelativeInertia.toBase p).Fiber U) :
    Functor.Fiber.fiberInclusion.map (autoHom (p := p) A) = A.1.auto.asIso.hom := rfl

omit [p.IsFibered] in
@[simp]
private lemma fiberInclusion_map_fiberAuto {U : 𝒞} (A : (RelativeInertia.toBase p).Fiber U) :
    (Functor.Fiber.fiberInclusion.map (fiberAuto (p := p) A)).hom = A.1.auto.asIso.hom := rfl

variable [(RelativeInertia.toBase p).IsFibered]

/-- The automorphism of the chosen pullback of `A` in the inertia, transported to the fibre of `p`
along the comparison isomorphism of `π`, is the base change of the automorphism of `A`. -/
private lemma mapPullbackFiberIso_fiberAuto {U : 𝒞} (A : (RelativeInertia.toBase p).Fiber U)
    {V : 𝒞} (f : V ⟶ U) :
    ((isFibredOneMorphism_π p).mapPullbackFiberIso A f).hom ≫
        (fiberπ (p := p) V).map
          (fiberAuto (Functor.pullbackFiber (RelativeInertia.toBase p) A f)) ≫
        ((isFibredOneMorphism_π p).mapPullbackFiberIso A f).inv =
      Functor.pullbackFiberHom (autoHom (p := p) A) f := by
  refine Functor.pullbackFiberHom_uniq (autoHom (p := p) A) f _ ?_
  have hcomm :
      (Functor.IsPreFibered.pullbackMap A.2 f).hom ≫ A.1.auto.asIso.hom =
        (Functor.pullbackFiber (RelativeInertia.toBase p) A f).1.auto.asIso.hom ≫
          (Functor.IsPreFibered.pullbackMap A.2 f).hom :=
    (Functor.IsPreFibered.pullbackMap A.2 f).comm
  simp only [Functor.map_comp, Category.assoc, fiberInclusion_map_autoHom,
    Functor.fiberInclusion_map_fiberFunctorOfCompEq_map, RelativeInertia.π_map,
    fiberInclusion_map_fiberAuto,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac]
  rw [← hcomm, ← Category.assoc]
  congr 1
  exact Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac (isFibredOneMorphism_π p) A f

/-- The image under `π` of the automorphism of the chosen pullback of `A` in the inertia is the
conjugate, by the comparison isomorphism of `π`, of the base change of the automorphism of `A`. -/
private lemma map_fiberAuto_pullbackFiber {U : 𝒞} (A : (RelativeInertia.toBase p).Fiber U)
    {V : 𝒞} (f : V ⟶ U) :
    (fiberπ (p := p) V).map
        (fiberAuto (Functor.pullbackFiber (RelativeInertia.toBase p) A f)) =
      ((isFibredOneMorphism_π p).mapPullbackFiberIso A f).inv ≫
        Functor.pullbackFiberHom (autoHom (p := p) A) f ≫
          ((isFibredOneMorphism_π p).mapPullbackFiberIso A f).hom := by
  rw [← mapPullbackFiberIso_fiberAuto (p := p) A f]
  simp

/-! ### The image of the map of morphism presheaves induced by `π`

A section of `Mor(A, B)` for the inertia is a morphism between the chosen pullbacks *in the
inertia*, i.e. a morphism of `𝒴` commuting with their automorphisms; `π` carries it to a section of
`Mor(π A, π B)`, injectively, and the image consists exactly of the sections that commute with the
base changes of the automorphisms of `A` and of `B`. Those two conditions are the two natural
endomorphisms `autoPre` and `autoPost` of `Mor(π A, π B)`. -/

/-- Precomposition with the base change of the automorphism of `A`, as a map of presheaves. -/
private noncomputable def autoPre {U : 𝒞} (A B : (RelativeInertia.toBase p).Fiber U) :
    Functor.morPresheaf p ((fiberπ (p := p) U).obj A) ((fiberπ (p := p) U).obj B) ⟶
      Functor.morPresheaf p ((fiberπ (p := p) U).obj A) ((fiberπ (p := p) U).obj B) :=
  Functor.morPresheafMap p (autoHom (p := p) A) (𝟙 _)

/-- Postcomposition with the base change of the automorphism of `B`, as a map of presheaves. -/
private noncomputable def autoPost {U : 𝒞} (A B : (RelativeInertia.toBase p).Fiber U) :
    Functor.morPresheaf p ((fiberπ (p := p) U).obj A) ((fiberπ (p := p) U).obj B) ⟶
      Functor.morPresheaf p ((fiberπ (p := p) U).obj A) ((fiberπ (p := p) U).obj B) :=
  Functor.morPresheafMap p (𝟙 _) (autoHom (p := p) B)

omit [(toBase p).IsFibered] in
@[simp]
private lemma autoPre_app {U : 𝒞} (A B : (RelativeInertia.toBase p).Fiber U) (g : (Over U)ᵒᵖ)
    (s : (Functor.morPresheaf p ((fiberπ (p := p) U).obj A) ((fiberπ (p := p) U).obj B)).obj g) :
    (autoPre (p := p) A B).app g s =
      Functor.pullbackFiberHom (autoHom (p := p) A) g.unop.hom ≫ s := by
  simp [autoPre]

omit [(toBase p).IsFibered] in
@[simp]
private lemma autoPost_app {U : 𝒞} (A B : (RelativeInertia.toBase p).Fiber U) (g : (Over U)ᵒᵖ)
    (s : (Functor.morPresheaf p ((fiberπ (p := p) U).obj A) ((fiberπ (p := p) U).obj B)).obj g) :
    (autoPost (p := p) A B).app g s =
      s ≫ Functor.pullbackFiberHom (autoHom (p := p) B) g.unop.hom := by
  simp [autoPost]

/-- Every section in the image of the map of morphism presheaves induced by `π` commutes with the
base changes of the two automorphisms: that commutation *is* the condition defining a morphism of
the inertia. -/
private lemma pullbackFiberHom_autoHom_conj {U : 𝒞} (A B : (RelativeInertia.toBase p).Fiber U)
    {V : 𝒞} (f : V ⟶ U)
    (m : Functor.pullbackFiber (RelativeInertia.toBase p) A f ⟶
      Functor.pullbackFiber (RelativeInertia.toBase p) B f) :
    Functor.pullbackFiberHom (autoHom (p := p) A) f ≫
        ((isFibredOneMorphism_π p).mapPullbackFiberIso A f).hom ≫
          (fiberπ (p := p) V).map m ≫
          ((isFibredOneMorphism_π p).mapPullbackFiberIso B f).inv =
      (((isFibredOneMorphism_π p).mapPullbackFiberIso A f).hom ≫
          (fiberπ (p := p) V).map m ≫
          ((isFibredOneMorphism_π p).mapPullbackFiberIso B f).inv) ≫
        Functor.pullbackFiberHom (autoHom (p := p) B) f := by
  have hm : fiberAuto (p := p) (Functor.pullbackFiber (RelativeInertia.toBase p) A f) ≫ m =
      m ≫ fiberAuto (p := p) (Functor.pullbackFiber (RelativeInertia.toBase p) B f) :=
    Functor.Fiber.hom_ext (RelativeInertiaHom.ext (Functor.Fiber.fiberInclusion.map m).comm.symm)
  have h := congrArg (fiberπ (p := p) V).map hm
  rw [Functor.map_comp, Functor.map_comp] at h
  rw [← mapPullbackFiberIso_fiberAuto (p := p) A f, ← mapPullbackFiberIso_fiberAuto (p := p) B f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  rw [← Category.assoc, ← Category.assoc, h]

/-- Conversely, a section of `Mor(π A, π B)` commuting with the base changes of the two
automorphisms is in the image of the map induced by `π`: the morphism of `𝒴` it conjugates to
commutes with the automorphisms of the chosen pullbacks in the inertia, hence is a morphism of the
inertia. -/
private lemma exists_conj_of_comm {U : 𝒞} (A B : (RelativeInertia.toBase p).Fiber U) {V : 𝒞}
    (f : V ⟶ U)
    (s : Functor.pullbackFiber p ((fiberπ (p := p) U).obj A) f ⟶
      Functor.pullbackFiber p ((fiberπ (p := p) U).obj B) f)
    (hs : Functor.pullbackFiberHom (autoHom (p := p) A) f ≫ s =
      s ≫ Functor.pullbackFiberHom (autoHom (p := p) B) f) :
    ∃ m : Functor.pullbackFiber (RelativeInertia.toBase p) A f ⟶
        Functor.pullbackFiber (RelativeInertia.toBase p) B f,
      ((isFibredOneMorphism_π p).mapPullbackFiberIso A f).hom ≫
          (fiberπ (p := p) V).map m ≫
          ((isFibredOneMorphism_π p).mapPullbackFiberIso B f).inv = s := by
  have hA := map_fiberAuto_pullbackFiber (p := p) A f
  have hB := map_fiberAuto_pullbackFiber (p := p) B f
  set ιA := (isFibredOneMorphism_π p).mapPullbackFiberIso A f with hιA
  set ιB := (isFibredOneMorphism_π p).mapPullbackFiberIso B f with hιB
  set t := ιA.inv ≫ s ≫ ιB.hom with ht
  have hconj : (fiberπ (p := p) V).map
        (fiberAuto (p := p) (Functor.pullbackFiber (RelativeInertia.toBase p) A f)) ≫ t =
      t ≫ (fiberπ (p := p) V).map
        (fiberAuto (p := p) (Functor.pullbackFiber (RelativeInertia.toBase p) B f)) := by
    rw [hA, hB, ht]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc s, ← hs]
    simp
  have hcomm : Functor.Fiber.fiberInclusion.map t ≫
        (Functor.pullbackFiber (RelativeInertia.toBase p) B f).1.auto.asIso.hom =
      (Functor.pullbackFiber (RelativeInertia.toBase p) A f).1.auto.asIso.hom ≫
        Functor.Fiber.fiberInclusion.map t := by
    have h := congrArg Functor.Fiber.fiberInclusion.map hconj
    rw [Functor.map_comp, Functor.map_comp] at h
    simp only [Functor.fiberInclusion_map_fiberFunctorOfCompEq_map, RelativeInertia.π_map,
      fiberInclusion_map_fiberAuto] at h
    exact h.symm
  refine ⟨⟨⟨Functor.Fiber.fiberInclusion.map t, hcomm⟩,
    (RelativeInertia.isHomLift_π_comp_iff (p := p) (𝟙 V) _).mpr t.2⟩, ?_⟩
  have hmt : (fiberπ (p := p) V).map
      (⟨⟨Functor.Fiber.fiberInclusion.map t, hcomm⟩,
        (RelativeInertia.isHomLift_π_comp_iff (p := p) (𝟙 V) _).mpr t.2⟩ :
        Functor.pullbackFiber (RelativeInertia.toBase p) A f ⟶
          Functor.pullbackFiber (RelativeInertia.toBase p) B f) = t :=
    Functor.Fiber.hom_ext rfl
  rw [hmt, ht]
  simp

/-! ### Condition (2) of Stacks 026F for the inertia

`Mor(A, B)` for the inertia maps injectively and naturally into `Mor(π A, π B)`, which is a sheaf,
and its image is *closed*: a section that is locally in the image commutes with the base changes of
the two automorphisms locally, hence everywhere, the target being separated. -/

/-- The map of morphism presheaves induced by `π` is injective in every degree, `π` being
faithful. -/
private lemma morPresheafMap_π_injective {U : 𝒞} (A B : (RelativeInertia.toBase p).Fiber U)
    (g : (Over U)ᵒᵖ) :
    Function.Injective (((isFibredOneMorphism_π p).morPresheafMap A B).app g) := by
  intro m n hmn
  simp only [Functor.IsFibredOneMorphism.morPresheafMap_app] at hmn
  have h2 : (fiberπ (p := p) g.unop.left).map m = (fiberπ (p := p) g.unop.left).map n := by
    rw [← cancel_epi ((isFibredOneMorphism_π p).mapPullbackFiberIso A g.unop.hom).hom,
      ← cancel_mono ((isFibredOneMorphism_π p).mapPullbackFiberIso B g.unop.hom).inv]
    simpa only [Category.assoc] using hmn
  exact Functor.Fiber.hom_ext
    ((RelativeInertia.π p).map_injective (congrArg Functor.Fiber.fiberInclusion.map h2))

/-- **Condition (2) of Stacks 026F for the absolute inertia.** If the presheaf `Mor(π A, π B)` of
`p` is a sheaf, so is the presheaf `Mor(A, B)` of the inertia. -/
private lemma isMorSheaf_toBase {J : GrothendieckTopology 𝒞} (U : 𝒞)
    (A B : (RelativeInertia.toBase p).Fiber U)
    (h : Functor.IsMorSheaf p J U ((fiberπ (p := p) U).obj A) ((fiberπ (p := p) U).obj B)) :
    Functor.IsMorSheaf (RelativeInertia.toBase p) J U A B := by
  unfold Functor.IsMorSheaf
  have hnat : ∀ {X Y : (Over U)ᵒᵖ} (k : X ⟶ Y)
      (m : (Functor.morPresheaf (RelativeInertia.toBase p) A B).obj X),
      ((isFibredOneMorphism_π p).morPresheafMap A B).app Y
          ((Functor.morPresheaf (RelativeInertia.toBase p) A B).map k m) =
        (Functor.morPresheaf p ((fiberπ (p := p) U).obj A) ((fiberπ (p := p) U).obj B)).map k
          (((isFibredOneMorphism_π p).morPresheafMap A B).app X m) := by
    intro X Y k m
    exact congrArg (fun φ ↦ φ m) (((isFibredOneMorphism_π p).morPresheafMap A B).naturality k)
  refine Presheaf.isSheaf_of_injective_natural
    (P := Functor.morPresheaf (RelativeInertia.toBase p) A B)
    (Q := Functor.morPresheaf p ((fiberπ (p := p) U).obj A) ((fiberπ (p := p) U).obj B))
    (fun g m ↦ ((isFibredOneMorphism_π p).morPresheafMap A B).app g m)
    (fun {X Y} k m ↦ hnat k m)
    (morPresheafMap_π_injective (p := p) A B) h ?_
  intro g S hS t hloc
  refine exists_conj_of_comm (p := p) A B g.hom t ?_
  have hkey : ∀ ⦃g' : Over U⦄ (k : g' ⟶ g), S k →
      (Functor.morPresheaf p ((fiberπ (p := p) U).obj A) ((fiberπ (p := p) U).obj B)).map k.op
          ((autoPre (p := p) A B).app (Opposite.op g) t) =
        (Functor.morPresheaf p ((fiberπ (p := p) U).obj A) ((fiberπ (p := p) U).obj B)).map k.op
          ((autoPost (p := p) A B).app (Opposite.op g) t) := by
    intro g' k hk
    obtain ⟨s, hs⟩ := hloc k hk
    rw [← (autoPre (p := p) A B).naturality_apply k.op t,
      ← (autoPost (p := p) A B).naturality_apply k.op t, ← hs]
    simp only [autoPre_app, autoPost_app, Functor.IsFibredOneMorphism.morPresheafMap_app]
    exact pullbackFiberHom_autoHom_conj (p := p) A B g'.hom s
  have hsep := ((isSheaf_iff_isSheaf_of_type (J.over U) _).1 h S hS).isSeparatedFor.ext hkey
  simpa only [autoPre_app, autoPost_app] using hsep

/-! ### Composing the maps of morphism presheaves of two 1-morphisms

The comparison isomorphisms of `CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso`
compose, and therefore so do the induced maps of morphism presheaves. This is what identifies the
map induced by `I_G` followed by the one induced by `π` with the one induced by `π` followed by the
one induced by `G`: the two composite 1-morphisms have the same underlying functor, and
`Functor.IsFibredOneMorphism` is a proposition. -/

universe u₆ u₇ u₈

/-- The comparison isomorphisms of two 1-morphisms compose to the comparison isomorphism of the
composite: both carry the image of the chosen cartesian lift to the chosen cartesian lift. -/
private lemma mapPullbackFiberIso_comp {𝒜 : Type u₆} [Category.{v} 𝒜] {ℬ : Type u₇}
    [Category.{v} ℬ] {𝒟 : Type u₈} [Category.{v} 𝒟] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {t : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ ℬ} {H : ℬ ⥤ 𝒟} [q.IsFibered] [r.IsFibered] [t.IsFibered]
    (hF : q.IsFibredOneMorphism r F) (hH : r.IsFibredOneMorphism t H) {U : 𝒞} (a : q.Fiber U)
    {V : 𝒞} (f : V ⟶ U) :
    ((hF.comp hH).mapPullbackFiberIso a f).hom =
      (hH.mapPullbackFiberIso ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a) f).hom ≫
        (Functor.fiberFunctorOfCompEq hH.comp_eq V).map (hF.mapPullbackFiberIso a f).hom := by
  have hcart : r.IsStronglyCartesian f (F.map (Functor.IsPreFibered.pullbackMap a.2 f)) :=
    hF.map_isStronglyCartesian f _ inferInstance
  have hcart' : t.IsStronglyCartesian f (H.map (F.map (Functor.IsPreFibered.pullbackMap a.2 f))) :=
    hH.map_isStronglyCartesian f _ hcart
  refine Functor.fiber_hom_ext_of_cartesian f
    (H.map (F.map (Functor.IsPreFibered.pullbackMap a.2 f))) inferInstance _ _ ?_
  rw [Functor.map_comp]
  simp only [Category.assoc, Functor.fiberInclusion_map_fiberFunctorOfCompEq_map]
  rw [← Functor.map_comp H, Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac hF a f,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac hH _ f]
  exact Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac (hF.comp hH) a f

/-- The inverse form of `mapPullbackFiberIso_comp`. -/
private lemma mapPullbackFiberIso_comp_inv {𝒜 : Type u₆} [Category.{v} 𝒜] {ℬ : Type u₇}
    [Category.{v} ℬ] {𝒟 : Type u₈} [Category.{v} 𝒟] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {t : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ ℬ} {H : ℬ ⥤ 𝒟} [q.IsFibered] [r.IsFibered] [t.IsFibered]
    (hF : q.IsFibredOneMorphism r F) (hH : r.IsFibredOneMorphism t H) {U : 𝒞} (a : q.Fiber U)
    {V : 𝒞} (f : V ⟶ U) :
    ((hF.comp hH).mapPullbackFiberIso a f).inv =
      (Functor.fiberFunctorOfCompEq hH.comp_eq V).map (hF.mapPullbackFiberIso a f).inv ≫
        (hH.mapPullbackFiberIso ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a) f).inv := by
  rw [← Iso.cancel_iso_hom_left ((hF.comp hH).mapPullbackFiberIso a f), Iso.hom_inv_id,
    mapPullbackFiberIso_comp hF hH a f]
  simp only [Category.assoc]
  rw [← Category.assoc ((Functor.fiberFunctorOfCompEq hH.comp_eq V).map
    (hF.mapPullbackFiberIso a f).hom), ← Functor.map_comp, Iso.hom_inv_id, Functor.map_id,
    Category.id_comp, Iso.hom_inv_id]

/-- The functor induced on fibres by a composite is the composite of the induced functors. -/
private lemma fiberFunctorOfCompEq_comp_map {𝒜 : Type u₆} [Category.{v} 𝒜] {ℬ : Type u₇}
    [Category.{v} ℬ] {𝒟 : Type u₈} [Category.{v} 𝒟] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {t : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ ℬ} {H : ℬ ⥤ 𝒟} (hF : q.IsFibredOneMorphism r F) (hH : r.IsFibredOneMorphism t H)
    {V : 𝒞} {x y : q.Fiber V} (m : x ⟶ y) :
    (Functor.fiberFunctorOfCompEq (hF.comp hH).comp_eq V).map m =
      (Functor.fiberFunctorOfCompEq hH.comp_eq V).map
        ((Functor.fiberFunctorOfCompEq hF.comp_eq V).map m) :=
  Functor.Fiber.hom_ext rfl

/-- **The maps of morphism presheaves of two 1-morphisms compose.** -/
private lemma morPresheafMap_comp {𝒜 : Type u₆} [Category.{v} 𝒜] {ℬ : Type u₇}
    [Category.{v} ℬ] {𝒟 : Type u₈} [Category.{v} 𝒟] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {t : 𝒟 ⥤ 𝒞}
    {F : 𝒜 ⥤ ℬ} {H : ℬ ⥤ 𝒟} [q.IsFibered] [r.IsFibered] [t.IsFibered]
    (hF : q.IsFibredOneMorphism r F) (hH : r.IsFibredOneMorphism t H) {U : 𝒞} (a b : q.Fiber U) :
    hF.morPresheafMap a b ≫
        hH.morPresheafMap ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a)
          ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj b) =
      (hF.comp hH).morPresheafMap a b := by
  ext g m
  change (hH.morPresheafMap ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a)
      ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj b)).app g
      ((hF.morPresheafMap a b).app g m) = ((hF.comp hH).morPresheafMap a b).app g m
  simp [Functor.IsFibredOneMorphism.morPresheafMap_app,
    mapPullbackFiberIso_comp hF hH a g.unop.hom, mapPullbackFiberIso_comp_inv hF hH b g.unop.hom,
    fiberFunctorOfCompEq_comp_map hF hH, Functor.map_comp, Category.assoc]

/-- The comparison isomorphism is natural in the morphism of the fibre. -/
@[reassoc]
private lemma mapPullbackFiberIso_naturality {𝒜 : Type u₆} [Category.{v} 𝒜] {ℬ : Type u₇}
    [Category.{v} ℬ] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {U : 𝒞} {a b : q.Fiber U} (φ : a ⟶ b) {V : 𝒞} (f : V ⟶ U) :
    (Functor.fiberFunctorOfCompEq hF.comp_eq V).map (Functor.pullbackFiberHom φ f) ≫
        (hF.mapPullbackFiberIso b f).inv =
      (hF.mapPullbackFiberIso a f).inv ≫
        Functor.pullbackFiberHom ((Functor.fiberFunctorOfCompEq hF.comp_eq U).map φ) f := by
  refine Functor.fiber_hom_ext_of_cartesian f
    (Functor.IsPreFibered.pullbackMap
      ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj b).2 f)
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc,
    Functor.fiberInclusion_map_fiberFunctorOfCompEq_map,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac,
    Functor.pullbackFiberHom_fac,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, Functor.pullbackFiberHom_fac]

/-- The base change of the image of a morphism of the fibre is the conjugate, by the comparison
isomorphisms, of the image of its base change. -/
private lemma pullbackFiberHom_map_eq {𝒜 : Type u₆} [Category.{v} 𝒜] {ℬ : Type u₇}
    [Category.{v} ℬ] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {U : 𝒞} {a b : q.Fiber U} (φ : a ⟶ b) {V : 𝒞} (f : V ⟶ U) :
    Functor.pullbackFiberHom ((Functor.fiberFunctorOfCompEq hF.comp_eq U).map φ) f =
      (hF.mapPullbackFiberIso a f).hom ≫
        (Functor.fiberFunctorOfCompEq hF.comp_eq V).map (Functor.pullbackFiberHom φ f) ≫
        (hF.mapPullbackFiberIso b f).inv := by
  rw [mapPullbackFiberIso_naturality hF φ f]
  simp

/-- The comparison isomorphism is compatible with iterated chosen pullbacks. -/
@[reassoc]
private lemma mapPullbackFiberIso_comp' {𝒜 : Type u₆} [Category.{v} 𝒜] {ℬ : Type u₇}
    [Category.{v} ℬ] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {U : 𝒞} (a : q.Fiber U) {V Z : 𝒞} (f : V ⟶ U) (γ : Z ⟶ V) :
    (Functor.fiberFunctorOfCompEq hF.comp_eq Z).map
          (Functor.pullbackFiberCompIso a f γ).hom ≫
        (hF.mapPullbackFiberIso a (γ ≫ f)).inv =
      (hF.mapPullbackFiberIso (Functor.pullbackFiber q a f) γ).inv ≫
        Functor.pullbackFiberHom (hF.mapPullbackFiberIso a f).inv γ ≫
        (Functor.pullbackFiberCompIso
          ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a) f γ).hom := by
  refine Functor.fiber_hom_ext_of_cartesian (γ ≫ f)
    (Functor.IsPreFibered.pullbackMap
      ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a).2 (γ ≫ f))
    (Functor.IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [CategoryTheory.Functor.map_comp, Category.assoc,
    Functor.fiberInclusion_map_fiberFunctorOfCompEq_map,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac,
    Functor.pullbackFiberCompIso_hom_fac, Functor.pullbackFiberHom_fac_assoc,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    Functor.pullbackFiberCompIso_hom_fac]

/-- `mapPullbackFiberIso_comp'` with the two contractions inverted, the form the base-change
compatibility of the transported descent datum uses. -/
@[reassoc]
private lemma mapPullbackFiberIso_comp_inv' {𝒜 : Type u₆} [Category.{v} 𝒜] {ℬ : Type u₇}
    [Category.{v} ℬ] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {U : 𝒞} (a : q.Fiber U) {V Z : 𝒞} (f : V ⟶ U) (γ : Z ⟶ V) :
    (hF.mapPullbackFiberIso a (γ ≫ f)).hom ≫
        (Functor.fiberFunctorOfCompEq hF.comp_eq Z).map
          (Functor.pullbackFiberCompIso a f γ).inv ≫
        (hF.mapPullbackFiberIso (Functor.pullbackFiber q a f) γ).inv =
      (Functor.pullbackFiberCompIso
          ((Functor.fiberFunctorOfCompEq hF.comp_eq U).obj a) f γ).inv ≫
        Functor.pullbackFiberHom (hF.mapPullbackFiberIso a f).hom γ := by
  have hγ : r.IsCartesian γ (Functor.IsPreFibered.pullbackMap
      ((Functor.fiberFunctorOfCompEq hF.comp_eq V).obj (Functor.pullbackFiber q a f)).2 γ) :=
    Functor.IsPreFibered.pullbackMap.IsCartesian _ _
  have hf : r.IsCartesian f (F.map (Functor.IsPreFibered.pullbackMap a.2 f)) :=
    hF.isCartesian_map_pullbackMap a f
  refine Functor.fiber_hom_ext_of_cartesian (γ ≫ f)
    (Functor.IsPreFibered.pullbackMap
      ((Functor.fiberFunctorOfCompEq hF.comp_eq V).obj (Functor.pullbackFiber q a f)).2 γ ≫
      F.map (Functor.IsPreFibered.pullbackMap a.2 f)) inferInstance _ _ ?_
  simp only [CategoryTheory.Functor.map_comp, Category.assoc,
    Functor.fiberInclusion_map_fiberFunctorOfCompEq_map,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac,
    Functor.pullbackFiberHom_fac_assoc, Functor.pullbackFiberCompIso_inv_fac,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc]
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    Functor.pullbackFiberCompIso_inv_fac,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac]

/-- The image under a 1-morphism of a descent datum: its objects are transported by the functors
induced on fibres and its gluing isomorphisms are conjugated by the comparison isomorphisms. -/
private noncomputable def sieveDescentDatumMap {𝒜 : Type u₆} [Category.{v} 𝒜] {ℬ : Type u₇}
    [Category.{v} ℬ] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {U : 𝒞} {R : Sieve U}
    (D : Functor.SieveDescentDatum q R) : Functor.SieveDescentDatum r R where
  obj {V} f hf := (Functor.fiberFunctorOfCompEq hF.comp_eq V).obj (D.obj f hf)
  iso {V W Z} {f} hf {g} hg ε ε' heq :=
    hF.mapPullbackFiberIso (D.obj f hf) ε ≪≫
      (Functor.fiberFunctorOfCompEq hF.comp_eq Z).mapIso (D.iso hf hg ε ε' heq) ≪≫
      (hF.mapPullbackFiberIso (D.obj g hg) ε').symm
  cocycle {V W X Z} {f} hf {g} hg {h} hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃ := by
    simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc, D.cocycle hf hg hh ε₁ ε₂ ε₃ h₁₂ h₂₃ h₁₃]
  iso_pullback {V W Z Z'} {f} hf {g} hg ε ε' heq γ := by
    simp only [Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_hom, Category.assoc,
      Functor.pullbackFiberIso_hom, Functor.pullbackFiberHom_comp]
    rw [← D.iso_pullback hf hg ε ε' heq γ]
    simp only [Functor.pullbackFiberIso_hom, CategoryTheory.Functor.map_comp, Category.assoc,
      ← mapPullbackFiberIso_comp_inv'_assoc hF (D.obj f hf) ε γ]
    rw [← mapPullbackFiberIso_naturality_assoc hF (D.iso hf hg ε ε' heq).hom γ,
      ← mapPullbackFiberIso_comp' hF (D.obj g hg) ε' γ]

/-- The map of morphism presheaves induced by a 1-morphism is compatible with the functoriality of
`Mor(x, y)` in the two objects of the fibre. -/
private lemma morPresheafMap_conj {𝒜 : Type u₆} [Category.{v} 𝒜] {ℬ : Type u₇}
    [Category.{v} ℬ] {q : 𝒜 ⥤ 𝒞} {r : ℬ ⥤ 𝒞} {F : 𝒜 ⥤ ℬ} [q.IsFibered] [r.IsFibered]
    (hF : q.IsFibredOneMorphism r F) {U : 𝒞} {x x' y y' : q.Fiber U} (e : x' ⟶ x) (e' : y ⟶ y') :
    hF.morPresheafMap x y ≫ Functor.morPresheafMap r
        ((Functor.fiberFunctorOfCompEq hF.comp_eq U).map e)
        ((Functor.fiberFunctorOfCompEq hF.comp_eq U).map e') =
      Functor.morPresheafMap q e e' ≫ hF.morPresheafMap x' y' := by
  ext g m
  simp [Functor.morPresheafMap_app, Functor.IsFibredOneMorphism.morPresheafMap_app,
    pullbackFiberHom_map_eq hF e g.unop.hom, pullbackFiberHom_map_eq hF e' g.unop.hom,
    Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- `I_G` followed by `π` is `π` followed by `G`, on the nose. -/
private lemma functoriality_comp_π {p : 𝒳 ⥤ 𝒞} {p' : 𝒳' ⥤ 𝒞} {G : 𝒳 ⥤ 𝒳'} (h : G ⋙ p' = p) :
    RelativeInertia.functoriality p p' G h ⋙ RelativeInertia.π p' =
      RelativeInertia.π p ⋙ G := rfl

/-- **The commuting square of maps of morphism presheaves.** Both composites are the map induced by
the composite 1-morphism `I_G ⋙ π = π ⋙ G`, `Functor.IsFibredOneMorphism` being a proposition. -/
private lemma morPresheafMap_square {p : 𝒳 ⥤ 𝒞} {p' : 𝒳' ⥤ 𝒞} {G : 𝒳 ⥤ 𝒳'}
    [p.IsFibered] [p'.IsFibered] [(RelativeInertia.toBase p).IsFibered]
    [(RelativeInertia.toBase p').IsFibered] (hG : p.IsFibredOneMorphism p' G)
    {U : 𝒞} (A B : (RelativeInertia.toBase p).Fiber U) :
    (isFibredOneMorphism_functoriality hG).morPresheafMap A B ≫
        (isFibredOneMorphism_π p').morPresheafMap
          ((Functor.fiberFunctorOfCompEq
            (isFibredOneMorphism_functoriality hG).comp_eq U).obj A)
          ((Functor.fiberFunctorOfCompEq
            (isFibredOneMorphism_functoriality hG).comp_eq U).obj B) =
      (isFibredOneMorphism_π p).morPresheafMap A B ≫
        hG.morPresheafMap
          ((Functor.fiberFunctorOfCompEq (isFibredOneMorphism_π p).comp_eq U).obj A)
          ((Functor.fiberFunctorOfCompEq (isFibredOneMorphism_π p).comp_eq U).obj B) := by
  rw [morPresheafMap_comp, morPresheafMap_comp]

/-! ### Condition (3) of Stacks 026F for the inertia

A descent datum for the inertia is pushed along `π` to a descent datum for `p`, which descends to
an object `y₀` carrying cartesian morphisms `ζ f` from the objects of the datum. The automorphisms
of the datum, conjugated by the comparison of `ζ f` with the chosen cartesian lift of `f` at `y₀`,
form a family of automorphisms of the chosen pullbacks of `y₀` compatible with base change, hence
glue to an automorphism `α` of `y₀`; the pair `(y₀, α)` is the object the datum descends to. -/

/-- **Condition (3) of Stacks 026F for the absolute inertia**, and with it the effectivity half of
Stacks 036Y (1). -/
private lemma hasEffectiveDescent_toBase {J : GrothendieckTopology 𝒞}
    (hmor : ∀ (U : 𝒞) (x y : p.Fiber U), Functor.IsMorSheaf p J U x y)
    (heff : Functor.HasEffectiveDescent p J) :
    Functor.HasEffectiveDescent (RelativeInertia.toBase p) J := by
  intro U R hR D
  obtain ⟨y₀, ζ, hζcart, hζcompat⟩ :=
    heff R hR (sieveDescentDatumMap (isFibredOneMorphism_π p) D)
  have hehom : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
      Functor.Fiber.fiberInclusion.map (Functor.fiberIsoOfCartesian
          (z := Functor.pullbackFiber p y₀ f) f
          (Functor.IsPreFibered.pullbackMap y₀.2 f) (ζ f hf) inferInstance (hζcart f hf)).hom ≫
        ζ f hf = Functor.IsPreFibered.pullbackMap y₀.2 f :=
    fun _ _ _ ↦ Functor.fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have heinv : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
      Functor.Fiber.fiberInclusion.map (Functor.fiberIsoOfCartesian
          (z := Functor.pullbackFiber p y₀ f) f
          (Functor.IsPreFibered.pullbackMap y₀.2 f) (ζ f hf) inferInstance (hζcart f hf)).inv ≫
        Functor.IsPreFibered.pullbackMap y₀.2 f = ζ f hf :=
    fun _ _ _ ↦ Functor.fiberIsoOfCartesian_inv_fac _ _ _ _ _
  set θ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f →
      (Functor.pullbackFiber p y₀ f ≅ Functor.pullbackFiber p y₀ f) := fun {_} f hf ↦
    Functor.fiberIsoOfCartesian (z := Functor.pullbackFiber p y₀ f) f
        (Functor.IsPreFibered.pullbackMap y₀.2 f) (ζ f hf)
        inferInstance (hζcart f hf) ≪≫
      autoIso (p := p) (D.obj f hf) ≪≫
      (Functor.fiberIsoOfCartesian (z := Functor.pullbackFiber p y₀ f) f
        (Functor.IsPreFibered.pullbackMap y₀.2 f) (ζ f hf)
        inferInstance (hζcart f hf)).symm with hθdef
  have hθfac : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
      Functor.Fiber.fiberInclusion.map (θ f hf).hom ≫
          Functor.IsPreFibered.pullbackMap y₀.2 f =
        Functor.Fiber.fiberInclusion.map (Functor.fiberIsoOfCartesian
            (z := Functor.pullbackFiber p y₀ f) f
            (Functor.IsPreFibered.pullbackMap y₀.2 f) (ζ f hf) inferInstance (hζcart f hf)).hom ≫
          (D.obj f hf).1.auto.asIso.hom ≫ ζ f hf := by
    intro V f hf
    simp only [hθdef, Iso.trans_hom, Iso.symm_hom, CategoryTheory.Functor.map_comp,
      Category.assoc, autoIso_hom, fiberInclusion_map_autoHom]
    rw [heinv f hf]
  -- the family is compatible with base change
  have hθcompat : ∀ ⦃V W : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f) (γ : W ⟶ V) (b : W ⟶ U)
      (hb : γ ≫ f = b) (hb' : R.arrows b),
      (θ b hb').hom = (Functor.pullbackFiberCompIso' y₀ f γ b hb).inv ≫
        Functor.pullbackFiberHom (θ f hf).hom γ ≫
        (Functor.pullbackFiberCompIso' y₀ f γ b hb).hom := by
    intro V W f hf γ b hb hb'
    refine Functor.fiber_hom_ext_of_cartesian b (Functor.IsPreFibered.pullbackMap y₀.2 b)
      (Functor.IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
    -- the right-hand side, composed with the cartesian lift of `b`
    have hRHS : Functor.Fiber.fiberInclusion.map
          ((Functor.pullbackFiberCompIso' y₀ f γ b hb).inv ≫
            Functor.pullbackFiberHom (θ f hf).hom γ ≫
            (Functor.pullbackFiberCompIso' y₀ f γ b hb).hom) ≫
          Functor.IsPreFibered.pullbackMap y₀.2 b =
        (Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso' y₀ f γ b hb).inv ≫
          Functor.IsPreFibered.pullbackMap (Functor.pullbackFiber p y₀ f).2 γ ≫
          Functor.Fiber.fiberInclusion.map (Functor.fiberIsoOfCartesian
              (z := Functor.pullbackFiber p y₀ f) f
            (Functor.IsPreFibered.pullbackMap y₀.2 f) (ζ f hf) inferInstance (hζcart f hf)).hom) ≫
          (D.obj f hf).1.auto.asIso.hom ≫ ζ f hf := by
      simp only [CategoryTheory.Functor.map_comp, Category.assoc,
        Functor.pullbackFiberCompIso'_hom_fac, Functor.pullbackFiberHom_fac_assoc]
      rw [hθfac f hf]
    rw [hθfac b hb', hRHS]
    -- the comparison `u` from the chosen pullback of `y₀` along `b` into the object of the datum
    have hulift : p.IsHomLift γ
        (Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso' y₀ f γ b hb).inv ≫
          Functor.IsPreFibered.pullbackMap (Functor.pullbackFiber p y₀ f).2 γ ≫
          Functor.Fiber.fiberInclusion.map (Functor.fiberIsoOfCartesian
              (z := Functor.pullbackFiber p y₀ f) f
            (Functor.IsPreFibered.pullbackMap y₀.2 f) (ζ f hf) inferInstance
              (hζcart f hf)).hom) := by
      have h0 : p.IsHomLift (𝟙 W ≫ γ ≫ 𝟙 V)
        (Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso' y₀ f γ b hb).inv ≫
          Functor.IsPreFibered.pullbackMap (Functor.pullbackFiber p y₀ f).2 γ ≫
          Functor.Fiber.fiberInclusion.map (Functor.fiberIsoOfCartesian
              (z := Functor.pullbackFiber p y₀ f) f
            (Functor.IsPreFibered.pullbackMap y₀.2 f) (ζ f hf) inferInstance
              (hζcart f hf)).hom) := inferInstance
      simpa using h0
    have hu : (Functor.Fiber.fiberInclusion.map
          (Functor.pullbackFiberCompIso' y₀ f γ b hb).inv ≫
          Functor.IsPreFibered.pullbackMap (Functor.pullbackFiber p y₀ f).2 γ ≫
          Functor.Fiber.fiberInclusion.map (Functor.fiberIsoOfCartesian
              (z := Functor.pullbackFiber p y₀ f) f
            (Functor.IsPreFibered.pullbackMap y₀.2 f) (ζ f hf) inferInstance
              (hζcart f hf)).hom) ≫ ζ f hf =
        Functor.IsPreFibered.pullbackMap y₀.2 b := by
      simp only [Category.assoc]
      rw [hehom f hf, Functor.pullbackFiberCompIso'_inv_fac]
    -- the underlying morphisms of the chosen cartesian lift in the inertia and of the gluing datum
    have hn : p.IsStronglyCartesian γ ((RelativeInertia.π p).map
        (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 γ)) :=
      isStronglyCartesian_hom γ (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 γ) inferInstance
    have hγid : γ = 𝟙 W ≫ γ := (Category.id_comp γ).symm
    set s := Functor.IsStronglyCartesian.map p γ
      ((RelativeInertia.π p).map (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 γ)) hγid
      (Functor.Fiber.fiberInclusion.map (Functor.pullbackFiberCompIso' y₀ f γ b hb).inv ≫
        Functor.IsPreFibered.pullbackMap (Functor.pullbackFiber p y₀ f).2 γ ≫
        Functor.Fiber.fiberInclusion.map (Functor.fiberIsoOfCartesian
            (z := Functor.pullbackFiber p y₀ f) f
          (Functor.IsPreFibered.pullbackMap y₀.2 f) (ζ f hf) inferInstance (hζcart f hf)).hom)
      with hsdef
    have hslift : p.IsHomLift (𝟙 W) s :=
      Functor.IsStronglyCartesian.map_isHomLift p γ _ hγid _
    have hs : s ≫ (RelativeInertia.π p).map
        (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 γ) = _ :=
      Functor.IsStronglyCartesian.fac p γ _ hγid _
    set Ψ := D.iso hf hb' γ (𝟙 W) (by rw [Category.id_comp]; exact hb) with hΨ
    set mI := Functor.Fiber.fiberInclusion.map Ψ.hom ≫
      Functor.IsPreFibered.pullbackMap (D.obj b hb').2 (𝟙 W) with hmI
    have hmcomm : (RelativeInertia.π p).map mI ≫ (D.obj b hb').1.auto.asIso.hom =
        (Functor.pullbackFiber (RelativeInertia.toBase p) (D.obj f hf) γ).1.auto.asIso.hom ≫
          (RelativeInertia.π p).map mI := mI.comm
    have hncomm : (RelativeInertia.π p).map
          (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 γ) ≫ (D.obj f hf).1.auto.asIso.hom =
        (Functor.pullbackFiber (RelativeInertia.toBase p) (D.obj f hf) γ).1.auto.asIso.hom ≫
          (RelativeInertia.π p).map (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 γ) :=
      (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 γ).comm
    have hmlift : p.IsHomLift (𝟙 W) ((RelativeInertia.π p).map mI) := by
      rw [hmI]
      have h0 : (RelativeInertia.toBase p).IsHomLift (𝟙 W ≫ 𝟙 W)
        (Functor.Fiber.fiberInclusion.map Ψ.hom ≫
          Functor.IsPreFibered.pullbackMap (D.obj b hb').2 (𝟙 W)) := inferInstance
      rw [Category.comp_id] at h0
      exact (RelativeInertia.isHomLift_π_comp_iff (p := p) (𝟙 W) _).mp h0
    -- the gluing datum identifies the two routes to `y₀`
    have hζc := hζcompat hf hb' γ (𝟙 W) (by rw [Category.id_comp]; exact hb)
    simp only [sieveDescentDatumMap, Iso.trans_hom, Iso.symm_hom,
      CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp, Category.assoc,
      Functor.fiberInclusion_map_fiberFunctorOfCompEq_map,
      Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc] at hζc
    have hmζ : (RelativeInertia.π p).map mI ≫ ζ b hb' =
        (RelativeInertia.π p).map (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 γ) ≫
          ζ f hf := by
      refine (cancel_epi (Functor.Fiber.fiberInclusion.map
        ((isFibredOneMorphism_π p).mapPullbackFiberIso (D.obj f hf) γ).hom)).1 ?_
      rw [Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac_assoc, hmI,
        CategoryTheory.Functor.map_comp]
      simpa only [Category.assoc] using hζc
    -- `s ≫ m` is the comparison at `b`
    have hsm : s ≫ (RelativeInertia.π p).map mI =
        Functor.Fiber.fiberInclusion.map (Functor.fiberIsoOfCartesian
            (z := Functor.pullbackFiber p y₀ b) b
          (Functor.IsPreFibered.pullbackMap y₀.2 b) (ζ b hb') inferInstance
            (hζcart b hb')).hom := by
      have hcb : p.IsStronglyCartesian b (ζ b hb') := inferInstance
      have hl1 : p.IsHomLift (𝟙 W) (s ≫ (RelativeInertia.π p).map mI) := by
        have h0 : p.IsHomLift (𝟙 W ≫ 𝟙 W) (s ≫ (RelativeInertia.π p).map mI) := inferInstance
        simpa using h0
      refine Functor.IsStronglyCartesian.ext p b (ζ b hb') (𝟙 W) ?_
      rw [hehom b hb', Category.assoc, hmζ, ← Category.assoc, hs, hu]
    -- put the pieces together
    rw [← hsm, ← hs]
    simp only [Category.assoc]
    rw [← Category.assoc ((RelativeInertia.π p).map
        (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 γ)) (D.obj f hf).1.auto.asIso.hom (ζ f hf),
      hncomm, Category.assoc, ← hmζ,
      ← Category.assoc ((RelativeInertia.π p).map mI) (D.obj b hb').1.auto.asIso.hom (ζ b hb'),
      hmcomm, Category.assoc]
  obtain ⟨α, hα⟩ := Functor.exists_fiberIso_of_locally p (hmor U) hR θ hθcompat
  -- the descended object of the inertia
  have hcomm : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
      ζ f hf ≫ Functor.Fiber.fiberInclusion.map α.hom =
        (D.obj f hf).1.auto.asIso.hom ≫ ζ f hf := by
    intro V f hf
    have h1 := Functor.pullbackFiberHom_fac α.hom f
    rw [hα f hf, hθfac f hf] at h1
    refine (cancel_epi (Functor.Fiber.fiberInclusion.map
      (Functor.fiberIsoOfCartesian (z := Functor.pullbackFiber p y₀ f) f
        (Functor.IsPreFibered.pullbackMap y₀.2 f) (ζ f hf) inferInstance (hζcart f hf)).hom)).1 ?_
    rw [← Category.assoc, hehom f hf]
    exact h1.symm
  have hαhi : Functor.Fiber.fiberInclusion.map α.hom ≫
      Functor.Fiber.fiberInclusion.map α.inv = 𝟙 y₀.1 := by
    rw [← CategoryTheory.Functor.map_comp, α.hom_inv_id]
    exact CategoryTheory.Functor.map_id _ _
  have hαih : Functor.Fiber.fiberInclusion.map α.inv ≫
      Functor.Fiber.fiberInclusion.map α.hom = 𝟙 y₀.1 := by
    rw [← CategoryTheory.Functor.map_comp, α.inv_hom_id]
    exact CategoryTheory.Functor.map_id _ _
  set Y : RelativeInertia p :=
    ⟨y₀.1, ⟨Functor.Fiber.fiberInclusion.map α.hom, Functor.Fiber.fiberInclusion.map α.inv,
      hαhi, hαih⟩,
      map_eq_id_of_isHomLift_id (p := p) U (Functor.Fiber.fiberInclusion.map α.hom)⟩ with hYdef
  refine ⟨Functor.Fiber.mk (show (RelativeInertia.toBase p).obj Y = U from y₀.2),
    fun {V} f hf ↦ ⟨ζ f hf, hcomm f hf⟩, ?_, ?_⟩
  · intro V f hf
    have h1 : p.IsCartesian f (ζ f hf) := hζcart f hf
    have h2 : (RelativeInertia.toBase p).IsStronglyCartesian f
        ((⟨ζ f hf, hcomm f hf⟩ : (D.obj f hf).1 ⟶ Y)) :=
      isStronglyCartesian_of_hom f _ inferInstance
    exact inferInstance
  · intro V W Z f hf g hg ε ε' heq
    refine RelativeInertiaHom.ext ?_
    have hζc := hζcompat hf hg ε ε' heq
    simp only [sieveDescentDatumMap, Iso.trans_hom, Iso.symm_hom,
      CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp, Category.assoc,
      Functor.fiberInclusion_map_fiberFunctorOfCompEq_map,
      Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc] at hζc
    have hgoal : Functor.Fiber.fiberInclusion.map
          ((isFibredOneMorphism_π p).mapPullbackFiberIso (D.obj f hf) ε).hom ≫
        ((RelativeInertia.π p).map (Functor.Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom) ≫
          (RelativeInertia.π p).map (Functor.IsPreFibered.pullbackMap (D.obj g hg).2 ε') ≫
          ζ g hg) =
      Functor.Fiber.fiberInclusion.map
          ((isFibredOneMorphism_π p).mapPullbackFiberIso (D.obj f hf) ε).hom ≫
        ((RelativeInertia.π p).map (Functor.IsPreFibered.pullbackMap (D.obj f hf).2 ε) ≫
          ζ f hf) := by
      rw [Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac_assoc]
      simpa only [Category.assoc] using hζc
    exact (cancel_epi _).1 hgoal

/-! ### Condition (1) of Stacks 02ZN for `I_G` -/

section Stackification

variable {p : 𝒳 ⥤ 𝒞} {p' : 𝒳' ⥤ 𝒞} {G : 𝒳 ⥤ 𝒳'} {J : GrothendieckTopology 𝒞}
  [p.IsFibered] [p'.IsFibered] [(RelativeInertia.toBase p).IsFibered]
  [(RelativeInertia.toBase p').IsFibered]

omit [(toBase p).IsFibered] [(toBase p').IsFibered] in
/-- The automorphism of `I_G A` is the image under `G` of the automorphism of `A`. -/
private lemma autoHom_functoriality (hG : p.IsFibredOneMorphism p' G) {U : 𝒞}
    (A : (RelativeInertia.toBase p).Fiber U) :
    autoHom (p := p')
        ((Functor.fiberFunctorOfCompEq (isFibredOneMorphism_functoriality hG).comp_eq U).obj A) =
      (Functor.fiberFunctorOfCompEq hG.comp_eq U).map (autoHom (p := p) A) :=
  Functor.Fiber.hom_ext rfl

/-- **Local injectivity for `I_G`.** The map induced by `I_G` followed by the injective map induced
by `π` is the map induced by `π` followed by the locally injective map induced by `G`. -/
private lemma isLocallyInjective_functoriality (hG : p.IsFibredOneMorphism p' G) {U : 𝒞}
    (A B : (RelativeInertia.toBase p).Fiber U)
    (hli : Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap
      ((Functor.fiberFunctorOfCompEq (isFibredOneMorphism_π p).comp_eq U).obj A)
      ((Functor.fiberFunctorOfCompEq (isFibredOneMorphism_π p).comp_eq U).obj B))) :
    Presheaf.IsLocallyInjective (J.over U)
      ((isFibredOneMorphism_functoriality hG).morPresheafMap A B) := by
  have := hli
  have hπli : Presheaf.IsLocallyInjective (J.over U)
      ((isFibredOneMorphism_π p).morPresheafMap A B) :=
    Presheaf.isLocallyInjective_of_injective (J.over U) _
      (morPresheafMap_π_injective (p := p) A B)
  exact Presheaf.isLocallyInjective_of_isLocallyInjective_fac (J.over U)
    (morPresheafMap_square hG A B)

/-- **Local surjectivity for `I_G`.** A section of `Mor(I_G A, I_G B)` is, locally on the base, the
image under `G` of a section of `Mor(π A, π B)`; that section need not commute with the two
automorphisms, but its two composites with them have the same image under `G`, so by local
injectivity they agree on a further covering, where the section becomes a section of
`Mor(A, B)` for the inertia. -/
private lemma isLocallySurjective_functoriality (hG : p.IsFibredOneMorphism p' G) {U : 𝒞}
    (A B : (RelativeInertia.toBase p).Fiber U)
    (hli : Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap
      ((Functor.fiberFunctorOfCompEq (isFibredOneMorphism_π p).comp_eq U).obj A)
      ((Functor.fiberFunctorOfCompEq (isFibredOneMorphism_π p).comp_eq U).obj B)))
    (hls : Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap
      ((Functor.fiberFunctorOfCompEq (isFibredOneMorphism_π p).comp_eq U).obj A)
      ((Functor.fiberFunctorOfCompEq (isFibredOneMorphism_π p).comp_eq U).obj B))) :
    Presheaf.IsLocallySurjective (J.over U)
      ((isFibredOneMorphism_functoriality hG).morPresheafMap A B) := by
  have := hli
  have := hls
  set A'' := (Functor.fiberFunctorOfCompEq
    (isFibredOneMorphism_functoriality hG).comp_eq U).obj A with hA''
  set B'' := (Functor.fiberFunctorOfCompEq
    (isFibredOneMorphism_functoriality hG).comp_eq U).obj B with hB''
  set πA := (Functor.fiberFunctorOfCompEq (isFibredOneMorphism_π p).comp_eq U).obj A with hπA
  set πB := (Functor.fiberFunctorOfCompEq (isFibredOneMorphism_π p).comp_eq U).obj B with hπB
  set ν := (isFibredOneMorphism_functoriality hG).morPresheafMap A B with hν
  set ν' := (isFibredOneMorphism_π p').morPresheafMap A'' B'' with hν'
  set μ := (isFibredOneMorphism_π p).morPresheafMap A B with hμ
  set ρ := hG.morPresheafMap πA πB with hρ
  have hsq : ν ≫ ν' = μ ≫ ρ := morPresheafMap_square hG A B
  have hconjA : ρ ≫ autoPre (p := p') A'' B'' = autoPre (p := p) A B ≫ ρ := by
    have h := morPresheafMap_conj hG (autoHom (p := p) A) (𝟙 πB)
    rwa [Functor.map_id, ← autoHom_functoriality hG A] at h
  have hconjB : ρ ≫ autoPost (p := p') A'' B'' = autoPost (p := p) A B ≫ ρ := by
    have h := morPresheafMap_conj hG (𝟙 πA) (autoHom (p := p) B)
    rwa [Functor.map_id, ← autoHom_functoriality hG B] at h
  constructor
  intro g n
  have hsqapp : ∀ (h : (Over U)ᵒᵖ)
      (m : (Functor.morPresheaf (RelativeInertia.toBase p) A B).obj h),
      ν'.app h (ν.app h m) = ρ.app h (μ.app h m) := fun h m ↦
    congrArg (fun f ↦ f m) (NatTrans.congr_app hsq h)
  have hsq : ν ≫ ν' = μ ≫ ρ := morPresheafMap_square hG A B
  have hconjAapp : ∀ (h : (Over U)ᵒᵖ) (m : (Functor.morPresheaf p πA πB).obj h),
      (autoPre (p := p') A'' B'').app h (ρ.app h m) =
        ρ.app h ((autoPre (p := p) A B).app h m) := fun h m ↦
    congrArg (fun f ↦ f m) (NatTrans.congr_app hconjA h)
  have hconjBapp : ∀ (h : (Over U)ᵒᵖ) (m : (Functor.morPresheaf p πA πB).obj h),
      (autoPost (p := p') A'' B'').app h (ρ.app h m) =
        ρ.app h ((autoPost (p := p) A B).app h m) := fun h m ↦
    congrArg (fun f ↦ f m) (NatTrans.congr_app hconjB h)
  set n' := ν'.app (Opposite.op g) n with hn'
  have hn'comm : (autoPre (p := p') A'' B'').app (Opposite.op g) n' =
      (autoPost (p := p') A'' B'').app (Opposite.op g) n' := by
    rw [hn', hν']
    simp only [autoPre_app, autoPost_app, Functor.IsFibredOneMorphism.morPresheafMap_app]
    exact pullbackFiberHom_autoHom_conj (p := p') A'' B'' g.hom n
  refine (J.over U).transitive (Presheaf.imageSieve_mem (J.over U) ρ n') _ ?_
  rintro g₁ k ⟨m₁, hm₁raw⟩
  have hm₁ : ρ.app (Opposite.op g₁) m₁ =
      (Functor.morPresheaf p' ((fiberπ (p := p') U).obj A'')
        ((fiberπ (p := p') U).obj B'')).map k.op n' := hm₁raw
  rw [Presheaf.pullback_imageSieve]
  set n₁ := (Functor.morPresheaf (RelativeInertia.toBase p') A'' B'').map k.op n with hn₁
  refine (J.over U).superset_covering ?_
    (Presheaf.equalizerSieve_mem (J.over U) ρ
      ((autoPre (p := p) A B).app (Opposite.op g₁) m₁)
      ((autoPost (p := p) A B).app (Opposite.op g₁) m₁) ?_)
  · -- on the equalizer sieve the restricted section lies in the image of `ν`
    intro g₂ l hlraw
    have hl : (Functor.morPresheaf p πA πB).map l.op
          ((autoPre (p := p) A B).app (Opposite.op g₁) m₁) =
        (Functor.morPresheaf p πA πB).map l.op
          ((autoPost (p := p) A B).app (Opposite.op g₁) m₁) := hlraw
    have hl' : (autoPre (p := p) A B).app (Opposite.op g₂)
          ((Functor.morPresheaf p πA πB).map l.op m₁) =
        (autoPost (p := p) A B).app (Opposite.op g₂)
          ((Functor.morPresheaf p πA πB).map l.op m₁) := by
      rwa [(autoPre (p := p) A B).naturality_apply l.op m₁,
        (autoPost (p := p) A B).naturality_apply l.op m₁]
    obtain ⟨m₂, hm₂⟩ := exists_conj_of_comm (p := p) A B g₂.hom
      ((Functor.morPresheaf p πA πB).map l.op m₁) (by simpa using hl')
    have hm₂' : μ.app (Opposite.op g₂) m₂ = (Functor.morPresheaf p πA πB).map l.op m₁ := hm₂
    have key : ν'.app (Opposite.op g₂) (ν.app (Opposite.op g₂) m₂) =
        ν'.app (Opposite.op g₂)
          ((Functor.morPresheaf (RelativeInertia.toBase p') A'' B'').map l.op n₁) := by
      rw [hsqapp, hm₂', ρ.naturality_apply l.op m₁, hm₁,
        ν'.naturality_apply l.op n₁, hn₁, ν'.naturality_apply k.op n, ← hn']
      rfl
    exact ⟨m₂, morPresheafMap_π_injective (p := p') A'' B'' (Opposite.op g₂) key⟩
  · -- the two composites have the same image under the map induced by `G`
    have hgoal : ρ.app (Opposite.op g₁) ((autoPre (p := p) A B).app (Opposite.op g₁) m₁) =
        ρ.app (Opposite.op g₁) ((autoPost (p := p) A B).app (Opposite.op g₁) m₁) := by
      rw [← hconjAapp, ← hconjBapp, hm₁,
        (autoPre (p := p') A'' B'').naturality_apply k.op n',
        (autoPost (p := p') A'' B'').naturality_apply k.op n', hn'comm]
    exact hgoal

/-! ### Condition (2) of Stacks 02ZN for `I_G`

The essential surjectivity of `I_G` needs, for an object `(x', α')` of `I_{𝒳'}`, an object of `𝒳`
whose image carries `α'`. Locally on the base `x'` is `G y` by `hobj`, and `α'` transports to an
automorphism of `G y`; that automorphism descends to `y`, locally on the base, because the map of
morphism presheaves induced by `G` is locally surjective, and the descended morphism is invertible
after a further covering because that map is also locally injective. -/

omit [(toBase p).IsFibered] [(toBase p').IsFibered] in
/-- **Local descent of a morphism of a fibre along `G`.** A morphism `G x ⟶ G y` of the fibre over
`V` is, locally on `V`, the image under `G` of a morphism between the chosen pullbacks of `x` and
`y`. This is local surjectivity of the map of Stacks 042V read through the chosen cartesian
lifts. -/
private lemma exists_locally_descends (hG : p.IsFibredOneMorphism p' G) {V : 𝒞} (x y : p.Fiber V)
    (hls : Presheaf.IsLocallySurjective (J.over V) (hG.morPresheafMap x y))
    (β : (Functor.fiberFunctorOfCompEq hG.comp_eq V).obj x ⟶
      (Functor.fiberFunctorOfCompEq hG.comp_eq V).obj y) :
    ∃ R ∈ J V, ∀ ⦃W : 𝒞⦄ (b : W ⟶ V), R.arrows b →
      ∃ a : Functor.pullbackFiber p x b ⟶ Functor.pullbackFiber p y b,
        G.map (Functor.Fiber.fiberInclusion.map a) ≫
            G.map (Functor.IsPreFibered.pullbackMap y.2 b) =
          G.map (Functor.IsPreFibered.pullbackMap x.2 b) ≫
            Functor.Fiber.fiberInclusion.map β := by
  have := hls
  set σ := Functor.morSection p' ((Functor.fiberFunctorOfCompEq hG.comp_eq V).obj x)
    ((Functor.fiberFunctorOfCompEq hG.comp_eq V).obj y) β with hσ
  have hSmem : Presheaf.imageSieve (hG.morPresheafMap x y) σ ∈ (J.over V) (Over.mk (𝟙 V)) :=
    Presheaf.imageSieve_mem (J.over V) (hG.morPresheafMap x y) σ
  refine ⟨Sieve.overEquiv (Over.mk (𝟙 V)) (Presheaf.imageSieve (hG.morPresheafMap x y) σ),
    ((J.mem_over_iff _).1 hSmem), ?_⟩
  intro W b hb
  have hk := (Sieve.overEquiv_iff (Presheaf.imageSieve (hG.morPresheafMap x y) σ) b).1 hb
  set κ : Over.mk (b ≫ (Over.mk (𝟙 V) : Over V).hom) ⟶ (Over.mk (𝟙 V) : Over V) :=
    Over.homMk b with hκ
  have hk' : (Presheaf.imageSieve (hG.morPresheafMap x y) σ).arrows κ := hk
  set ι : (Over.mk b : Over V) ⟶ Over.mk (b ≫ (Over.mk (𝟙 V) : Over V).hom) :=
    Over.homMk (𝟙 W) (by simp) with hι
  obtain ⟨m, hm⟩ := (Presheaf.imageSieve (hG.morPresheafMap x y) σ).downward_closed hk' ι
  refine ⟨m, ?_⟩
  have hm' : (hG.morPresheafMap x y).app (Opposite.op (Over.mk b)) m =
      Functor.morRestrict p' ((Functor.fiberFunctorOfCompEq hG.comp_eq V).obj x)
        ((Functor.fiberFunctorOfCompEq hG.comp_eq V).obj y) (ι ≫ κ) σ := hm
  have hfac := congrArg (fun t ↦ Functor.Fiber.fiberInclusion.map t ≫
    Functor.IsPreFibered.pullbackMap
      ((Functor.fiberFunctorOfCompEq hG.comp_eq V).obj y).2 (Over.mk b : Over V).hom) hm'
  simp only [Functor.IsFibredOneMorphism.morPresheafMap_app, Functor.map_comp, Category.assoc,
    Functor.fiberInclusion_map_fiberFunctorOfCompEq_map,
    Functor.IsFibredOneMorphism.mapPullbackFiberIso_inv_fac,
    Functor.morRestrict_fac, hσ, Functor.morSection] at hfac
  have hidy : Functor.Fiber.fiberInclusion.map
        (Functor.pullbackFiberIdIso ((Functor.fiberFunctorOfCompEq hG.comp_eq V).obj y)).inv ≫
      Functor.IsPreFibered.pullbackMap
        ((Functor.fiberFunctorOfCompEq hG.comp_eq V).obj y).2 (Over.mk (𝟙 V) : Over V).hom =
      𝟙 _ := Functor.pullbackFiberIdIso_inv_fac _
  have hidx : Functor.pullbackFiberMap p' ((Functor.fiberFunctorOfCompEq hG.comp_eq V).obj x)
        (ι ≫ κ) ≫ Functor.Fiber.fiberInclusion.map
        (Functor.pullbackFiberIdIso ((Functor.fiberFunctorOfCompEq hG.comp_eq V).obj x)).hom ≫
        Functor.Fiber.fiberInclusion.map β =
      Functor.IsPreFibered.pullbackMap
        ((Functor.fiberFunctorOfCompEq hG.comp_eq V).obj x).2 (Over.mk b : Over V).hom ≫
        Functor.Fiber.fiberInclusion.map β := by
    rw [← Category.assoc, Functor.pullbackFiberIdIso_hom_fac]
    congr 1
    exact Functor.pullbackFiberMap_fac p' _ (ι ≫ κ)
  rw [hidy, Category.comp_id, hidx] at hfac
  have hxfac := Functor.IsFibredOneMorphism.mapPullbackFiberIso_hom_fac hG x
    (Over.mk b : Over V).hom
  rw [← hxfac, Category.assoc] at hfac
  exact (cancel_epi _).1 hfac

omit [(toBase p').IsFibered] in
/-- **Local essential surjectivity for `I_G`.** For an object `(x', α')` of `I_{𝒳'}` there is a
covering sieve of `p' x'` along each member of which `(x', α')` receives a strongly cartesian
morphism from an object of the form `I_G A`. Locally on the base `x'` is `G y` by `hobj`, and `α'`
transports through the cartesian lift to an automorphism `β` of `G y`; `β` descends to the chosen
pullback of `y` on a further covering, and the descended morphism becomes invertible on a third,
which produces the object `A` of `I_𝒳`. -/
private lemma exists_covering_functoriality (hG : p.IsFibredOneMorphism p' G)
    (hmor : ∀ (V : 𝒞) (x y : p.Fiber V),
      Presheaf.IsLocallyInjective (J.over V) (hG.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (J.over V) (hG.morPresheafMap x y))
    (hobj : ∀ x' : 𝒳', ∃ R ∈ J (p'.obj x'), ∀ ⦃V : 𝒞⦄ (f : V ⟶ p'.obj x'), R f →
      ∃ (y : 𝒳) (φ : G.obj y ⟶ x'), p'.IsStronglyCartesian f φ)
    (A' : RelativeInertia p') :
    ∃ R ∈ J ((RelativeInertia.toBase p').obj A'),
      ∀ ⦃V : 𝒞⦄ (f : V ⟶ (RelativeInertia.toBase p').obj A'), R f →
        ∃ (A : RelativeInertia p)
          (φ : (RelativeInertia.functoriality p p' G hG.comp_eq).obj A ⟶ A'),
          (RelativeInertia.toBase p').IsStronglyCartesian f φ := by
  refine ⟨⟨fun _ f ↦ ∃ (A : RelativeInertia p)
      (φ : (RelativeInertia.functoriality p p' G hG.comp_eq).obj A ⟶ A'),
      (RelativeInertia.toBase p').IsStronglyCartesian f φ, ?_⟩, ?_, fun _ _ hf ↦ hf⟩
  · -- the property is closed under precomposition: use a cartesian lift in `I_𝒳`
    intro V W f hf γ
    obtain ⟨A, φ, hφ⟩ := hf
    have := hφ
    have hAV : (RelativeInertia.toBase p).obj A = V := by
      have h1 : (RelativeInertia.toBase p').obj
          ((RelativeInertia.functoriality p p' G hG.comp_eq).obj A) = V :=
        IsHomLift.domain_eq (RelativeInertia.toBase p') f φ
      rw [Functor.comp_obj, RelativeInertia.π_obj]
      rw [← Functor.congr_obj hG.comp_eq A.obj]
      exact h1
    obtain ⟨A₁, ψ, hψc⟩ := IsPreFibered.exists_isCartesian (RelativeInertia.toBase p) hAV γ
    have := hψc
    have h1 := (isFibredOneMorphism_functoriality hG).map_isStronglyCartesian γ ψ inferInstance
    exact ⟨A₁, (RelativeInertia.functoriality p p' G hG.comp_eq).map ψ ≫ φ, inferInstance⟩
  · -- the property holds on a covering sieve
    obtain ⟨R₀, hR₀, hR₀prop⟩ := hobj A'.obj
    refine J.transitive hR₀ _ ?_
    intro V f hf
    obtain ⟨y, φ₀, hφ₀⟩ := hR₀prop f hf
    have := hφ₀
    have hyV : p.obj y = V := by
      rw [← Functor.congr_obj hG.comp_eq y]
      exact IsHomLift.domain_eq p' f φ₀
    obtain ⟨β, hβlift, hβfac⟩ := exists_auto_of_isStronglyCartesian (p := p') A' f φ₀ hφ₀
    set ŷ : p.Fiber V := Functor.Fiber.mk hyV with hŷ
    set βf : (Functor.fiberFunctorOfCompEq hG.comp_eq V).obj ŷ ≅
        (Functor.fiberFunctorOfCompEq hG.comp_eq V).obj ŷ :=
      Functor.Fiber.isoMk β hβlift with hβf
    have hβfhom : Functor.Fiber.fiberInclusion.map βf.hom = β.hom := rfl
    obtain ⟨R₁, hR₁, hR₁prop⟩ := exists_locally_descends hG ŷ ŷ (hmor V ŷ ŷ).2 βf.hom
    obtain ⟨R₂, hR₂, hR₂prop⟩ := exists_locally_descends hG ŷ ŷ (hmor V ŷ ŷ).2 βf.inv
    refine J.transitive (J.intersection_covering hR₁ hR₂) _ ?_
    intro W g hg
    obtain ⟨a₁, ha₁⟩ := hR₁prop g hg.1
    obtain ⟨a₂, ha₂⟩ := hR₂prop g hg.2
    -- `a₁` and `a₂` become mutually inverse after `G`
    have hWeq : p'.obj (G.obj (Functor.pullbackFiber p ŷ g).1) = W :=
      (Functor.congr_obj hG.comp_eq (Functor.pullbackFiber p ŷ g).1).trans
        (Functor.pullbackFiber p ŷ g).2
    have := hG.map_isStronglyCartesian g (Functor.IsPreFibered.pullbackMap ŷ.2 g) inferInstance
    have := IsHomLift.id (p := p') hWeq
    have hli := (hmor V ŷ ŷ).1
    have hcomp : ∀ (a b : Functor.pullbackFiber p ŷ g ⟶ Functor.pullbackFiber p ŷ g)
        (u v : G.obj (Functor.Fiber.fiberInclusion.obj ŷ) ⟶
          G.obj (Functor.Fiber.fiberInclusion.obj ŷ)),
        G.map (Functor.Fiber.fiberInclusion.map a) ≫
            G.map (Functor.IsPreFibered.pullbackMap ŷ.2 g) =
          G.map (Functor.IsPreFibered.pullbackMap ŷ.2 g) ≫ u →
        G.map (Functor.Fiber.fiberInclusion.map b) ≫
            G.map (Functor.IsPreFibered.pullbackMap ŷ.2 g) =
          G.map (Functor.IsPreFibered.pullbackMap ŷ.2 g) ≫ v → u ≫ v = 𝟙 _ →
        Sieve.overEquiv (Over.mk g)
          (Presheaf.equalizerSieve (F := Functor.morPresheaf p ŷ ŷ)
            (X := Opposite.op (Over.mk g)) (a ≫ b) (𝟙 (Functor.pullbackFiber p ŷ g))) ∈ J W := by
      intro a b u v ha hb huv
      have := hG.map_isHomLift (𝟙 W) (Functor.Fiber.fiberInclusion.map (a ≫ b))
      have hab : G.map (Functor.Fiber.fiberInclusion.map (a ≫ b)) =
          𝟙 (G.obj (Functor.pullbackFiber p ŷ g).1) := by
        refine Functor.IsStronglyCartesian.ext p' g
          (G.map (Functor.IsPreFibered.pullbackMap ŷ.2 g)) (𝟙 W) ?_
        simp only [Functor.map_comp, Category.assoc]
        rw [hb, ← Category.assoc, ha, Category.assoc, huv]
        exact (Category.comp_id _).trans (Category.id_comp _).symm
      have happ : (hG.morPresheafMap ŷ ŷ).app (Opposite.op (Over.mk g)) (a ≫ b) =
          (hG.morPresheafMap ŷ ŷ).app (Opposite.op (Over.mk g))
            (𝟙 (Functor.pullbackFiber p ŷ g)) := by
        have hFG : (Functor.fiberFunctorOfCompEq hG.comp_eq (Over.mk g : Over V).left).map
              (a ≫ b) =
            (Functor.fiberFunctorOfCompEq hG.comp_eq (Over.mk g : Over V).left).map
              (𝟙 (Functor.pullbackFiber p ŷ g)) :=
          Functor.Fiber.hom_ext (by
            simp only [Functor.fiberInclusion_map_fiberFunctorOfCompEq_map, Functor.map_id]
            exact hab)
        rw [Functor.IsFibredOneMorphism.morPresheafMap_app,
          Functor.IsFibredOneMorphism.morPresheafMap_app, hFG]
      exact (J.mem_over_iff _).1
        (Presheaf.equalizerSieve_mem (J.over V) (hG.morPresheafMap ŷ ŷ) _ _ happ)
    have hβinv : Functor.Fiber.fiberInclusion.map βf.hom ≫
        Functor.Fiber.fiberInclusion.map βf.inv = 𝟙 _ := by
      simp [← Functor.map_comp]
    have hβinv' : Functor.Fiber.fiberInclusion.map βf.inv ≫
        Functor.Fiber.fiberInclusion.map βf.hom = 𝟙 _ := by
      simp [← Functor.map_comp]
    refine J.superset_covering ?_ (J.intersection_covering (hcomp a₁ a₂ _ _ ha₁ ha₂ hβinv)
      (hcomp a₂ a₁ _ _ ha₂ ha₁ hβinv'))
    intro W' h hh
    obtain ⟨hh12, hh21⟩ := hh
    set k : (Over.mk (h ≫ g) : Over V) ⟶ Over.mk g := Over.homMk h with hkdef
    -- the restrictions of `a₁` and `a₂` are mutually inverse
    have hiso : ∀ a b : Functor.pullbackFiber p ŷ g ⟶ Functor.pullbackFiber p ŷ g,
        (Sieve.overEquiv (Over.mk g) (Presheaf.equalizerSieve (F := Functor.morPresheaf p ŷ ŷ)
          (X := Opposite.op (Over.mk g)) (a ≫ b) (𝟙 (Functor.pullbackFiber p ŷ g)))).arrows h →
        Functor.Fiber.fiberInclusion.map (Functor.morRestrict p ŷ ŷ k a) ≫
          Functor.Fiber.fiberInclusion.map (Functor.morRestrict p ŷ ŷ k b) =
        𝟙 (Functor.pullbackFiber p ŷ (h ≫ g)).1 := by
      intro a b hab
      have he : Functor.morRestrict p ŷ ŷ k (a ≫ b) =
          Functor.morRestrict p ŷ ŷ k (𝟙 (Functor.pullbackFiber p ŷ g)) :=
        (Sieve.overEquiv_iff (Y := (Over.mk g : Over V)) _ h).1 hab
      have hid : Functor.morRestrict p ŷ ŷ k (𝟙 (Functor.pullbackFiber p ŷ g)) =
          𝟙 (Functor.pullbackFiber p ŷ (h ≫ g)) := Functor.morRestrict_id_hom p ŷ k
      rw [Functor.morRestrict_comp_hom, hid] at he
      rw [← CategoryTheory.Functor.map_comp, he]
      exact CategoryTheory.Functor.map_id _ _
    -- the descended automorphism, and its compatibility with `β`
    have ha₁' : G.map (Functor.Fiber.fiberInclusion.map a₁) ≫
        G.map (Functor.IsPreFibered.pullbackMap ŷ.2 (Over.mk g : Over V).hom) =
      G.map (Functor.IsPreFibered.pullbackMap ŷ.2 (Over.mk g : Over V).hom) ≫
        Functor.Fiber.fiberInclusion.map βf.hom := ha₁
    have hrel : G.map (Functor.Fiber.fiberInclusion.map (Functor.morRestrict p ŷ ŷ k a₁)) ≫
        G.map (Functor.IsPreFibered.pullbackMap ŷ.2 (h ≫ g)) =
      G.map (Functor.IsPreFibered.pullbackMap ŷ.2 (h ≫ g)) ≫ β.hom := by
      have h1 := congrArg G.map (Functor.morRestrict_fac p ŷ ŷ k a₁)
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
        CategoryTheory.Functor.map_comp] at h1
      refine h1.trans ?_
      rw [ha₁', ← Category.assoc, ← CategoryTheory.Functor.map_comp,
        Functor.pullbackFiberMap_fac, hβfhom]
      rfl
    refine ⟨⟨(Functor.pullbackFiber p ŷ (h ≫ g)).1,
      ⟨Functor.Fiber.fiberInclusion.map (Functor.morRestrict p ŷ ŷ k a₁),
        Functor.Fiber.fiberInclusion.map (Functor.morRestrict p ŷ ŷ k a₂), hiso a₁ a₂ hh12,
        hiso a₂ a₁ hh21⟩,
        map_eq_id_of_isHomLift_id (p := p) W'
          (Functor.Fiber.fiberInclusion.map (Functor.morRestrict p ŷ ŷ k a₁))⟩,
      ⟨G.map (Functor.IsPreFibered.pullbackMap ŷ.2 (h ≫ g)) ≫ φ₀, ?_⟩, ?_⟩
    · change (G.map (Functor.IsPreFibered.pullbackMap ŷ.2 (h ≫ g)) ≫ φ₀) ≫ A'.auto.asIso.hom =
        G.map (Functor.Fiber.fiberInclusion.map (Functor.morRestrict p ŷ ŷ k a₁)) ≫
          G.map (Functor.IsPreFibered.pullbackMap ŷ.2 (h ≫ g)) ≫ φ₀
      rw [← Category.assoc, hrel, Category.assoc, Category.assoc, hβfac]
    · have h1 : p'.IsStronglyCartesian (h ≫ g)
          (G.map (Functor.IsPreFibered.pullbackMap ŷ.2 (h ≫ g))) :=
        hG.map_isStronglyCartesian (h ≫ g) _ inferInstance
      exact isStronglyCartesian_of_hom (p := p') ((h ≫ g) ≫ f) _ inferInstance

end Stackification

end RelativeInertia

end Helpers

/-- **The stackification of the inertia is the inertia of the stackification.** Let `(𝒞, J)` be a
site, let `p : 𝒳 ⥤ 𝒞` be a fibred category over `𝒞` and let `G : 𝒳 ⥤ 𝒳'` be the stackification
of `𝒳` (Stacks 02ZN): a 1-morphism `hG` of fibred categories over `𝒞` whose target `p'` is a
stack, such that (`hmor`) for every `U` and all `x`, `y` in `𝒳_U` the induced map
`Mor(x, y) ⟶ Mor(G x, G y)` of presheaves on `𝒞/U` is locally injective and locally surjective,
its target being a sheaf, and such that (`hobj`) every object `x'` of `𝒳'` admits a covering
sieve `R` of `p'.obj x'` with `x'|_V` in the essential image of `𝒳_V ⥤ 𝒳'_V` for every
`f : V ⟶ p'.obj x'` in `R`.

Then the inertia `I_{𝒳'}` is a stack over `𝒞`, and the functoriality 1-morphism
`I_G : I_𝒳 ⥤ I_{𝒳'}`, `(x, α) ↦ (G x, G α)`, is a stackification of the inertia `I_𝒳`: it is a
1-morphism of fibred categories over `𝒞` and it satisfies the same two conditions. -/
@[stacks 06NS]
public theorem RelativeInertia.isStackification_functoriality
    {p : 𝒳 ⥤ 𝒞} {p' : 𝒳' ⥤ 𝒞} {G : 𝒳 ⥤ 𝒳'} {J : GrothendieckTopology 𝒞} [p.IsFibered]
    (hG : p.IsFibredOneMorphism p' G) (hp' : p'.IsStack J)
    (hmor : haveI : p'.IsFibered := hp'.isFibered
      ∀ (U : 𝒞) (x y : p.Fiber U),
        Presheaf.IsLocallyInjective (J.over U)
            (Functor.IsFibredOneMorphism.morPresheafMap hG x y) ∧
          Presheaf.IsLocallySurjective (J.over U)
            (Functor.IsFibredOneMorphism.morPresheafMap hG x y))
    (hobj : ∀ x' : 𝒳', ∃ R ∈ J (p'.obj x'), ∀ ⦃V : 𝒞⦄ (f : V ⟶ p'.obj x'), R f →
      ∃ (y : 𝒳) (φ : G.obj y ⟶ x'), p'.IsStronglyCartesian f φ) :
    haveI : p'.IsFibered := hp'.isFibered
    haveI : (RelativeInertia.toBase p).IsFibered :=
      RelativeInertia.isFibered p p (𝟭 𝒞) inferInstance (Functor.isFibredOneMorphism_id p)
    haveI : (RelativeInertia.toBase p').IsFibered :=
      RelativeInertia.isFibered p' p' (𝟭 𝒞) hp'.isFibered (Functor.isFibredOneMorphism_id p')
    (RelativeInertia.toBase p').IsStack J ∧
      ∃ hIG : (RelativeInertia.toBase p).IsFibredOneMorphism (RelativeInertia.toBase p')
          (RelativeInertia.functoriality p p' G hG.comp_eq),
        (∀ (U : 𝒞) (A B : (RelativeInertia.toBase p).Fiber U),
            Presheaf.IsLocallyInjective (J.over U)
                (Functor.IsFibredOneMorphism.morPresheafMap hIG A B) ∧
              Presheaf.IsLocallySurjective (J.over U)
                (Functor.IsFibredOneMorphism.morPresheafMap hIG A B)) ∧
          ∀ A' : RelativeInertia p', ∃ R ∈ J ((RelativeInertia.toBase p').obj A'),
            ∀ ⦃V : 𝒞⦄ (f : V ⟶ (RelativeInertia.toBase p').obj A'), R f →
              ∃ (A : RelativeInertia p)
                (φ : (RelativeInertia.functoriality p p' G hG.comp_eq).obj A ⟶ A'),
                (RelativeInertia.toBase p').IsStronglyCartesian f φ := by
  have hp'fib := hp'.isFibered
  have hIfib : (RelativeInertia.toBase p).IsFibered :=
    RelativeInertia.isFibered p p (𝟭 𝒞) inferInstance (Functor.isFibredOneMorphism_id p)
  have hI'fib : (RelativeInertia.toBase p').IsFibered :=
    RelativeInertia.isFibered p' p' (𝟭 𝒞) hp'.isFibered (Functor.isFibredOneMorphism_id p')
  exact ⟨⟨hI'fib, fun U A B ↦ isMorSheaf_toBase (p := p') U A B (hp'.isMorSheaf U _ _),
      hasEffectiveDescent_toBase (p := p') hp'.isMorSheaf hp'.hasEffectiveDescent⟩,
    isFibredOneMorphism_functoriality hG,
    fun U A B ↦ ⟨isLocallyInjective_functoriality hG A B (hmor U _ _).1,
      isLocallySurjective_functoriality hG A B (hmor U _ _).1 (hmor U _ _).2⟩,
    exists_covering_functoriality hG hmor hobj⟩

end CategoryTheory

end
