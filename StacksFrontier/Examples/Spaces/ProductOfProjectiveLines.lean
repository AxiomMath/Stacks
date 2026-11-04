module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.CategoryTheory.Pullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper

/-!
# Infinite tuples of morphisms to the projective line

The functor `(ℙ¹)^∞` sends a scheme `T` to the set of sequences `(f₁, f₂, …)` of morphisms
`fᵢ : T ⟶ ℙ¹`. It satisfies the sheaf condition for the fpqc topology, being a product of
copies of the functor of points of `ℙ¹`, and its diagonal is representable: for two
scheme-valued points, given by sequences `f` on `T` and `g` on `S`, the fibre product
`T ×_F S` is the scheme-theoretic intersection of the closed subschemes
`T ×_{fᵢ, ℙ¹, gᵢ} S` of `T × S`.

That intersection is built here for an arbitrary family of pairs of morphisms into a
separated scheme: the equalizer of each pair is a closed subscheme, and the subscheme cut out
by the supremum of their ideal sheaves is their intersection, which has the universal property
of the limit of the family because each inclusion is a monomorphism.

## Main definitions

* `AlgebraicGeometry.interEqualizer`: the scheme-theoretic intersection of the equalizers of a
  family of pairs of morphisms `T ⟶ P` with `P` separated, a closed subscheme of `T`.
* `AlgebraicGeometry.powPresheaf`: the functor of `ι`-indexed tuples of morphisms to a scheme.
* `AlgebraicGeometry.powPresheaf.fibre`: the fibre product of two scheme-valued points of that
  functor.
* `AlgebraicGeometry.projectiveLinePow`: the functor `(ℙ¹)^∞`.

## Main results

* `AlgebraicGeometry.interEqualizerLift_ι` and `AlgebraicGeometry.interEqualizerι_comp`: the
  universal property of the intersection of the equalizers.
* `AlgebraicGeometry.isSheaf_powPresheaf`: tuples of morphisms to a scheme form a sheaf for
  every subcanonical topology, in particular for the fpqc topology.
* `AlgebraicGeometry.relativelyRepresentable_diag_powPresheaf`: the diagonal of that functor is
  representable as soon as the target scheme is separated.
* `AlgebraicGeometry.isSheaf_fpqc_projectiveLinePow` and
  `AlgebraicGeometry.relativelyRepresentable_diag_projectiveLinePow`: the two statements for
  `(ℙ¹)^∞`.

## Implementation notes

The index set of the sequences is `ULift ℕ`, so that the functor takes values in the same
universe as the morphism spaces of `Scheme.{u}`. The sheaf condition is checked on presieves
and reduces to the one for the functor of points of `ℙ¹`, which holds because the fpqc
topology is subcanonical. Representability of the diagonal is obtained from the equivalent
condition of Stacks 0024, `CategoryTheory.yoneda_relativelyRepresentable_diag_tfae`: every
scheme-valued point is a representable morphism. The representing scheme is the intersection
of the equalizers of the two component families inside the product of the two schemes, cut out
by the supremum of the corresponding ideal sheaves; the factorization property comes from the
universal property of a closed immersion, `AlgebraicGeometry.IsClosedImmersion.lift`, and
uniqueness from the fact that a closed immersion is a monomorphism.

### No `@[stacks 078F]`

Tag 078F asserts the existence of a functor `Sch^{opp} ⥤ Sets` which satisfies the sheaf
condition for the fpqc topology, has representable diagonal, receives a surjective flat
universally open quasi-compact morphism from a scheme, and is *not* an algebraic space. Only
the first two properties of the witness `(ℙ¹)^∞` are proved here, so the tag appears only in
scoped form. Missing are:

* the morphism `(SL₂)^∞ ⟶ (ℙ¹)^∞` induced by the smooth surjective affine morphism
  `SL₂ ⟶ ℙ¹`, together with the facts that `(SL₂)^∞` is an affine scheme and that the morphism
  is surjective, flat, universally open and quasi-compact. The infinite product is not the
  obstruction: a small diagram of affine schemes has a limit in schemes and that limit is
  affine, by `AlgebraicGeometry.Scheme.affineLimitCone`, so an arbitrary product of copies of
  an affine scheme is available. What is missing is the morphism `SL₂ ⟶ ℙ¹`, and, for
  surjectivity, flatness and universal openness of the induced morphism, the behaviour of
  faithful flatness under infinite fibre products over an arbitrary base scheme. The
  construction of the induced morphism out of a product of copies of an affine scheme, and its
  quasi-compactness, are in
  `StacksFrontier/Examples/Spaces/ProductOfProjectiveLinesCover.lean`;
* the failure of `(ℙ¹)^∞` to be an algebraic space. That argument needs the vanishing of
  cohomology of quasi-coherent sheaves above a cutoff on a quasi-compact separated algebraic
  space (Stacks 072B), together with a quasi-coherent sheaf on `(ℙ¹)^∞` whose cohomology is
  nonzero in degree `n`, for every `n`: the pullback of `𝒪(-2, …, -2)` along the projection
  `(ℙ¹)^∞ ⟶ (ℙ¹)ⁿ`.

## References

* [Stacks Project, Tag 078F](https://stacks.math.columbia.edu/tag/078F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section InterEqualizer

variable {ι : Type*} {T P : Scheme.{u}} [P.IsSeparated] (f g : ι → (T ⟶ P))

/-- The ideal sheaf on `T` cutting out the common equalizer of the pairs `f i`, `g i`: the
supremum of the ideal sheaves of the individual equalizers. -/
def interEqualizerIdeal : T.IdealSheafData :=
  ⨆ i, (equalizer.ι (f i) (g i)).ker

/-- The scheme-theoretic intersection of the equalizers of `f i` and `g i`, as a closed
subscheme of `T`. -/
def interEqualizer : Scheme.{u} := (interEqualizerIdeal f g).subscheme

/-- The closed immersion of the common equalizer of the families `f` and `g` into `T`. -/
def interEqualizerι : interEqualizer f g ⟶ T := (interEqualizerIdeal f g).subschemeι

/-- The inclusion of the intersection of the equalizers into `T` is a closed immersion. -/
instance : IsClosedImmersion (interEqualizerι f g) :=
  inferInstanceAs (IsClosedImmersion (interEqualizerIdeal f g).subschemeι)

/-- The inclusion of the intersection of the equalizers into `T` is a monomorphism. -/
instance : Mono (interEqualizerι f g) :=
  inferInstanceAs (Mono (interEqualizerIdeal f g).subschemeι)

omit [P.IsSeparated] in
/-- The kernel of the inclusion of the intersection of the equalizers is the ideal sheaf that
cuts it out. -/
@[simp]
lemma ker_interEqualizerι : (interEqualizerι f g).ker = interEqualizerIdeal f g :=
  Scheme.IdealSheafData.ker_subschemeι _

omit [P.IsSeparated] in
/-- A morphism equalizing every pair `f i`, `g i` kills the ideal sheaf of the intersection of
the equalizers. -/
lemma interEqualizerIdeal_le_ker {W : Scheme.{u}} (α : W ⟶ T)
    (h : ∀ i, α ≫ f i = α ≫ g i) : interEqualizerIdeal f g ≤ α.ker := by
  refine iSup_le fun i ↦ ?_
  rw [← equalizer.lift_ι α (h i)]
  exact Scheme.Hom.le_ker_comp _ _

/-- The factorization of a morphism equalizing every pair `f i`, `g i` through the
intersection of the equalizers. -/
def interEqualizerLift {W : Scheme.{u}} (α : W ⟶ T) (h : ∀ i, α ≫ f i = α ≫ g i) :
    W ⟶ interEqualizer f g :=
  IsClosedImmersion.lift (interEqualizerι f g) α
    (by rw [ker_interEqualizerι]; exact interEqualizerIdeal_le_ker f g α h)

omit [P.IsSeparated] in
/-- The factorization through the intersection of the equalizers recovers the morphism. -/
@[reassoc (attr := simp)]
lemma interEqualizerLift_ι {W : Scheme.{u}} (α : W ⟶ T) (h : ∀ i, α ≫ f i = α ≫ g i) :
    interEqualizerLift f g α h ≫ interEqualizerι f g = α :=
  IsClosedImmersion.lift_fac _ _ _

/-- The intersection of the equalizers does equalize every pair `f i`, `g i`. -/
lemma interEqualizerι_comp (i : ι) :
    interEqualizerι f g ≫ f i = interEqualizerι f g ≫ g i := by
  have H : (equalizer.ι (f i) (g i)).ker ≤ (interEqualizerι f g).ker := by
    rw [ker_interEqualizerι]
    exact le_iSup (fun j ↦ (equalizer.ι (f j) (g j)).ker) i
  have hfac : IsClosedImmersion.lift (equalizer.ι (f i) (g i)) (interEqualizerι f g) H ≫
      equalizer.ι (f i) (g i) = interEqualizerι f g :=
    IsClosedImmersion.lift_fac _ _ _
  rw [← hfac, Category.assoc, Category.assoc, equalizer.condition]

end InterEqualizer

/-- The functor of `ι`-indexed tuples of morphisms to a scheme `P`: the `ι`-fold product of the
functor of points of `P`. -/
@[simps]
def powPresheaf (ι : Type u) (P : Scheme.{u}) : Scheme.{u}ᵒᵖ ⥤ Type u where
  obj T := ι → (T.unop ⟶ P)
  map φ := ↾fun x i ↦ φ.unop ≫ x i

/-- Unification hint for `(powPresheaf ι P).obj (op W) = (ι → (W ⟶ P))`. -/
unif_hint powPresheaf_obj_eq_pi (ι ι' : Type u) (P P' W W' : Scheme.{u}) where
  ι ≟ ι'
  P ≟ P'
  W ≟ W' ⊢
  (powPresheaf ι P).obj (op W) ≟ (ι' → (W' ⟶ P'))

/-- A scheme-valued point of `powPresheaf ι P` is the tuple of its components. -/
lemma powPresheaf_app_eq {ι : Type u} {P V : Scheme.{u}} {W : Scheme.{u}ᵒᵖ}
    (G : yoneda.obj V ⟶ powPresheaf ι P) (β : W.unop ⟶ V) :
    G.app W β = fun i ↦ β ≫ yonedaEquiv G i := by
  simpa [yonedaEquiv_apply] using G.naturality_apply β.op (𝟙 V)

/-- A tuple of compatible families of morphisms to `P` glues whenever each single family
does. -/
lemma isSheafFor_powPresheaf {ι : Type u} {P X : Scheme.{u}} {R : Presieve X}
    (h : Presieve.IsSheafFor (yoneda.obj P) R) :
    Presieve.IsSheafFor (powPresheaf ι P) R := by
  classical
  intro x hx
  let y (i : ι) : Presieve.FamilyOfElements (yoneda.obj P) R := fun _ p hp ↦ x p hp i
  have hycomp (i : ι) : (y i).Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ p₁ p₂ h₁ h₂ e
    simpa [y] using congrFun (hx g₁ g₂ h₁ h₂ e) i
  choose t ht ht' using fun i ↦ h (y i) (hycomp i)
  refine ⟨t, ?_, ?_⟩
  · intro Y p hp
    funext i
    simpa [y] using ht i p hp
  · intro s hs
    funext i
    exact ht' i (s i) fun Y p hp ↦ by simpa [y] using congrFun (hs p hp) i

/-- Tuples of morphisms to a scheme form a sheaf for every subcanonical topology. -/
lemma isSheaf_powPresheaf {ι : Type u} {P : Scheme.{u}}
    (J : GrothendieckTopology Scheme.{u}) [J.Subcanonical] :
    Presheaf.IsSheaf J (powPresheaf ι P) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS
  exact isSheafFor_powPresheaf
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj P) S hS)

namespace powPresheaf

variable {ι : Type u} {P : Scheme.{u}} [P.IsSeparated] {U V : Scheme.{u}}
  (A : yoneda.obj U ⟶ powPresheaf ι P) (B : yoneda.obj V ⟶ powPresheaf ι P)

/-- The fibre product of two scheme-valued points of `powPresheaf ι P`: the intersection,
inside `U × V`, of the equalizers of the two component families. -/
def fibre : Scheme.{u} :=
  interEqualizer (fun i ↦ (prod.fst : U ⨯ V ⟶ U) ≫ yonedaEquiv A i)
    (fun i ↦ (prod.snd : U ⨯ V ⟶ V) ≫ yonedaEquiv B i)

/-- The closed immersion of the fibre product into `U × V`. -/
def fibreι : fibre A B ⟶ U ⨯ V := interEqualizerι _ _

/-- The closed immersion of the fibre product into `U × V` is a monomorphism. -/
instance : Mono (fibreι A B) := inferInstanceAs (Mono (interEqualizerι ..))

/-- On the fibre product the two component families agree. -/
lemma fibreι_comp (i : ι) :
    fibreι A B ≫ prod.fst ≫ yonedaEquiv A i = fibreι A B ≫ prod.snd ≫ yonedaEquiv B i :=
  interEqualizerι_comp _ _ i

/-- A pair of morphisms whose component families agree factors through the fibre product. -/
def fibreLift {W : Scheme.{u}} (α : W ⟶ U) (β : W ⟶ V)
    (h : ∀ i, α ≫ yonedaEquiv A i = β ≫ yonedaEquiv B i) : W ⟶ fibre A B :=
  interEqualizerLift _ _ (prod.lift α β) fun i ↦ by simpa using h i

omit [P.IsSeparated] in
/-- The factorization through the fibre product recovers the pair of morphisms. -/
@[reassoc (attr := simp)]
lemma fibreLift_ι {W : Scheme.{u}} (α : W ⟶ U) (β : W ⟶ V)
    (h : ∀ i, α ≫ yonedaEquiv A i = β ≫ yonedaEquiv B i) :
    fibreLift A B α β h ≫ fibreι A B = prod.lift α β :=
  interEqualizerLift_ι ..

/-- The two projections of the fibre product agree after composing with `A` and `B`. -/
lemma comm_fibre :
    yoneda.map (fibreι A B ≫ prod.fst) ≫ A = yoneda.map (fibreι A B ≫ prod.snd) ≫ B := by
  apply yonedaEquiv.injective
  rw [← yonedaEquiv_naturality, ← yonedaEquiv_naturality]
  funext i
  simpa using fibreι_comp A B i

omit [P.IsSeparated] in
/-- The component families of a pullback cone over `A` and `B` agree pointwise. -/
lemma coneCondition (s : PullbackCone A B) (W : Scheme.{u}ᵒᵖ) (z : s.pt.obj W) (i : ι) :
    s.fst.app W z ≫ yonedaEquiv A i = s.snd.app W z ≫ yonedaEquiv B i := by
  have h₁ : A.app W (s.fst.app W z) = fun j ↦ s.fst.app W z ≫ yonedaEquiv A j :=
    powPresheaf_app_eq A _
  have h₂ : B.app W (s.snd.app W z) = fun j ↦ s.snd.app W z ≫ yonedaEquiv B j :=
    powPresheaf_app_eq B _
  have h : A.app W (s.fst.app W z) = B.app W (s.snd.app W z) := by
    have h₀ : (s.fst ≫ A).app W z = (s.snd ≫ B).app W z := by rw [s.condition]
    simpa only [NatTrans.comp_app, CategoryTheory.comp_apply] using h₀
  rw [h₁, h₂] at h
  exact congrFun h i

/-- The morphism from the apex of a pullback cone over `A` and `B` to the fibre product. -/
def coneLift (s : PullbackCone A B) : s.pt ⟶ yoneda.obj (fibre A B) where
  app W := ↾fun z ↦ fibreLift A B (s.fst.app W z) (s.snd.app W z) (coneCondition A B s W z)
  naturality W W' φ := by
    refine ConcreteCategory.hom_ext _ _ fun z ↦ ?_
    rw [← cancel_mono (fibreι A B)]
    simp only [CategoryTheory.comp_apply, TypeCat.ofHom_apply, yoneda_obj_map, fibreLift_ι,
      Category.assoc]
    have h₁ := s.fst.naturality_apply φ z
    have h₂ := s.snd.naturality_apply φ z
    simp only [yoneda_obj_map, TypeCat.ofHom_apply] at h₁ h₂
    rw [h₁, h₂, prod.comp_lift]

omit [P.IsSeparated] in
/-- The components of the morphism induced by a pullback cone. -/
@[simp]
lemma coneLift_app (s : PullbackCone A B) (W : Scheme.{u}ᵒᵖ) (z : s.pt.obj W) :
    (coneLift A B s).app W z =
      fibreLift A B (s.fst.app W z) (s.snd.app W z) (coneCondition A B s W z) :=
  rfl

/-- Morphisms of presheaves are equal if they agree on all sections. -/
private lemma ext_of_app_apply {F G : Scheme.{u}ᵒᵖ ⥤ Type u} {a b : F ⟶ G}
    (h : ∀ W z, a.app W z = b.app W z) : a = b :=
  NatTrans.ext (funext fun W ↦ ConcreteCategory.hom_ext _ _ (h W))

/-- Composing the morphism induced by a pullback cone with a morphism out of the fibre product
and evaluating at a section. -/
private lemma coneLift_comp_app {ι : Type u} {P U V : Scheme.{u}}
    (A : yoneda.obj U ⟶ powPresheaf ι P) (B : yoneda.obj V ⟶ powPresheaf ι P)
    (s : PullbackCone A B) {X : Scheme.{u}} (q : U ⨯ V ⟶ X)
    (W : Scheme.{u}ᵒᵖ) (z : s.pt.obj W) :
    (coneLift A B s ≫ yoneda.map (fibreι A B ≫ q)).app W z =
      prod.lift (s.fst.app W z) (s.snd.app W z) ≫ q := by
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply, yoneda_map_app, TypeCat.ofHom_apply,
    coneLift_app]
  rw [← Category.assoc, fibreLift_ι]

omit [P.IsSeparated] in
/-- The morphism induced by a pullback cone is compatible with the first projection. -/
@[simp]
lemma coneLift_fst (s : PullbackCone A B) :
    coneLift A B s ≫ yoneda.map (fibreι A B ≫ prod.fst) = s.fst := by
  refine ext_of_app_apply fun W z ↦ ?_
  rw [coneLift_comp_app, prod.lift_fst]

omit [P.IsSeparated] in
/-- The morphism induced by a pullback cone is compatible with the second projection. -/
@[simp]
lemma coneLift_snd (s : PullbackCone A B) :
    coneLift A B s ≫ yoneda.map (fibreι A B ≫ prod.snd) = s.snd := by
  refine ext_of_app_apply fun W z ↦ ?_
  rw [coneLift_comp_app, prod.lift_snd]

omit [P.IsSeparated] in
/-- The morphism to the fibre product induced by a pullback cone is the only one compatible
with the two projections. -/
lemma coneLift_uniq (s : PullbackCone A B) (m : s.pt ⟶ yoneda.obj (fibre A B))
    (h₁ : m ≫ yoneda.map (fibreι A B ≫ prod.fst) = s.fst)
    (h₂ : m ≫ yoneda.map (fibreι A B ≫ prod.snd) = s.snd) :
    m = coneLift A B s := by
  refine ext_of_app_apply fun W z ↦ ?_
  have e₁ : (m ≫ yoneda.map (fibreι A B ≫ prod.fst)).app W z = s.fst.app W z := by rw [h₁]
  have e₂ : (m ≫ yoneda.map (fibreι A B ≫ prod.snd)).app W z = s.snd.app W z := by rw [h₂]
  simp only [NatTrans.comp_app, CategoryTheory.comp_apply, yoneda_map_app,
    TypeCat.ofHom_apply] at e₁ e₂
  rw [coneLift_app, ← cancel_mono (fibreι A B), fibreLift_ι]
  refine prod.hom_ext ?_ ?_
  · simpa [Category.assoc] using e₁
  · simpa [Category.assoc] using e₂

/-- The fibre product of two scheme-valued points of `powPresheaf ι P` represents the fibre
product of the corresponding morphisms of presheaves. -/
lemma isPullback_fibre :
    IsPullback (yoneda.map (fibreι A B ≫ prod.fst)) (yoneda.map (fibreι A B ≫ prod.snd)) A B :=
  IsPullback.of_isLimit (PullbackCone.IsLimit.mk (comm_fibre A B)
    (coneLift A B) (coneLift_fst A B) (coneLift_snd A B) (coneLift_uniq A B))

end powPresheaf

variable {ι : Type u} {P : Scheme.{u}} [P.IsSeparated]

/-- Every scheme-valued point of `powPresheaf ι P` is a representable morphism of presheaves,
when `P` is separated. -/
theorem relativelyRepresentable_yonedaEquiv_symm_powPresheaf (U : Scheme.{u})
    (ξ : (powPresheaf ι P).obj (op U)) :
    yoneda.relativelyRepresentable (yonedaEquiv.symm ξ) := fun {_} G ↦
  ⟨powPresheaf.fibre (yonedaEquiv.symm ξ) G, powPresheaf.fibreι _ G ≫ prod.snd,
    yoneda.map (powPresheaf.fibreι _ G ≫ prod.fst), powPresheaf.isPullback_fibre _ G⟩

/-- The diagonal of the functor of `ι`-tuples of morphisms to a separated scheme is
representable. -/
theorem relativelyRepresentable_diag_powPresheaf :
    yoneda.relativelyRepresentable (diag (powPresheaf ι P)) :=
  ((yoneda_relativelyRepresentable_diag_tfae (powPresheaf ι P)).out 2 1).mp
    relativelyRepresentable_yonedaEquiv_symm_powPresheaf

/-- The integral model of projective `n`-space is separated, being proper over the terminal
scheme. -/
instance isSeparated_projectiveSpaceAtUniverse (n : ℕ) :
    Scheme.IsSeparated (projectiveSpaceAtUniverse.{u} n) := by
  have := isProper_terminalFrom_projectiveSpaceAtUniverse.{u} n
  exact ⟨inferInstance⟩

/-- The functor `(ℙ¹)^∞` sending a scheme `T` to the set of sequences of morphisms
`T ⟶ ℙ¹`. -/
def projectiveLinePow : Scheme.{u}ᵒᵖ ⥤ Type u :=
  powPresheaf (ULift.{u} ℕ) (projectiveSpaceAtUniverse.{u} 1)

/-- `(ℙ¹)^∞` satisfies the sheaf condition for the fpqc topology. -/
@[stacks 078F "the witness (P^1)^∞ is a sheaf for the fpqc topology"]
theorem isSheaf_fpqc_projectiveLinePow :
    Presheaf.IsSheaf Scheme.fpqcTopology.{u} projectiveLinePow.{u} :=
  isSheaf_powPresheaf _

/-- The diagonal of `(ℙ¹)^∞` is representable. -/
@[stacks 078F "the witness (P^1)^∞ has representable diagonal"]
theorem relativelyRepresentable_diag_projectiveLinePow :
    yoneda.relativelyRepresentable (diag projectiveLinePow.{u}) :=
  relativelyRepresentable_diag_powPresheaf

end AlgebraicGeometry

end
