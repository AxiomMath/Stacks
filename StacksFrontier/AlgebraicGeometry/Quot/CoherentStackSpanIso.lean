module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCategory
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomFpqcDescentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcChartFullness

/-!
# Comparing two morphisms of `Coh_{X/Y}` out of one object on a common algebraic space

Let `m₁ : A ⟶ A₁` and `m₂ : A ⟶ A₂` be two morphisms of `Coh_{X/Y}` (Stacks 08KB) with a common
source.  Each carries an isomorphism of the inverse image of the module of its target with the
module of `A`, along the induced morphism of base changes.  Given an algebraic space `Z` mapping
to the base change `X_A` of `A`, the two composites `Z ⟶ X_A ⟶ X_{A₁}` and `Z ⟶ X_A ⟶ X_{A₂}`
pull the modules of `A₁` and `A₂` back to `Z`, and the two isomorphisms identify both with the
inverse image of the module of `A`; composing one identification with the inverse of the other is
an isomorphism of the two inverse images on `Z`.  That is
`AlgebraicGeometry.Space.CoherentHom.spanIso`.

This is the shape in which a descent datum for `Coh_{X/Y}` becomes a descent datum of
quasi-coherent modules on algebraic spaces (Stacks 04W3): its pairwise isomorphisms are the span
isomorphisms of the two morphisms out of the object over a pairwise fibre product, read on the
pairwise fibre product of the base changes.  The three laws below are what the cocycle condition
of the module datum needs: span isomorphisms compose, they are compatible with a further inverse
image, and they are unchanged by precomposing both morphisms with a third one.

## Main definitions

* `AlgebraicGeometry.Space.CoherentHom.spanIso`: the span isomorphism.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.compComparison_app`: the comparison of inverse images
  of the composition of `Coh_{X/Y}`, at one module, is the comparison
  `AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison` of the descent files.
* `AlgebraicGeometry.Space.CoherentHom.spanIso_trans` and
  `AlgebraicGeometry.Space.CoherentHom.spanIso_refl`: span isomorphisms compose.
* `AlgebraicGeometry.Space.CoherentHom.spanIso_pullback`: they are compatible with inverse image.
* `AlgebraicGeometry.Space.CoherentHom.spanIso_comp`: they are unchanged by precomposition.

## References

* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent (pullbackComparison pullbackComparison_trans
  pullbackComparison_naturality pullbackComparison_inv_naturality)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- The comparison of inverse images of the composition of `Coh_{X/Y}`, at one module, is the
comparison of Stacks 03LU at the factorization `X_h ≫ X_{h'} = X_{h ≫ h'}`. -/
theorem compComparison_app {T T' T'' : SchemesOver D.Y} (h : T ⟶ T') (h' : T' ⟶ T'')
    (M : Modules.{u, u} B S hS (D.space T'').1 (D.space T'').2) :
    (D.compComparison h h').app M =
      pullbackComparison B S hS (D.relativeMap h) (D.relativeMap h') (D.relativeMap (h ≫ h'))
        (baseChangeMap_comp D.f h h').symm M :=
  modulePullbackTriangle_app _ M

end CoherentSituation

namespace CoherentHom

variable {D : CoherentSituation B S hS} {A A₁ A₂ A₃ : CoherentObject D}

/-- **The span isomorphism of two morphisms of `Coh_{X/Y}` out of one object.**  For
`m₁ : A ⟶ A₁`, `m₂ : A ⟶ A₂` and `r : Z ⟶ X_A`, with `r₁` and `r₂` the composites of `r` with the
two induced morphisms of base changes, the isomorphism of the inverse images along `r₁` and `r₂` of
the modules of `A₁` and `A₂` which reads both, through the two module comparisons, as the inverse
image along `r` of the module of `A`. -/
def spanIso (m₁ : CoherentHom A A₁) (m₂ : CoherentHom A A₂) {Z : AlgebraicSpaces B S hS}
    (r : Z ⟶ D.space A.T) (r₁ : Z ⟶ D.space A₁.T) (r₂ : Z ⟶ D.space A₂.T)
    (h₁ : r ≫ D.relativeMap m₁.base = r₁) (h₂ : r ≫ D.relativeMap m₂.base = r₂) :
    (modulePullback B S hS r₁).obj A₁.F ≅ (modulePullback B S hS r₂).obj A₂.F :=
  pullbackComparison B S hS r (D.relativeMap m₁.base) r₁ h₁ A₁.F ≪≫
    (modulePullback B S hS r).mapIso (asIso m₁.fibre) ≪≫
    (modulePullback B S hS r).mapIso (asIso m₂.fibre).symm ≪≫
    (pullbackComparison B S hS r (D.relativeMap m₂.base) r₂ h₂ A₂.F).symm

/-- The forward morphism of a span isomorphism, written out. -/
theorem spanIso_hom (m₁ : CoherentHom A A₁) (m₂ : CoherentHom A A₂) {Z : AlgebraicSpaces B S hS}
    (r : Z ⟶ D.space A.T) (r₁ : Z ⟶ D.space A₁.T) (r₂ : Z ⟶ D.space A₂.T)
    (h₁ : r ≫ D.relativeMap m₁.base = r₁) (h₂ : r ≫ D.relativeMap m₂.base = r₂) :
    (spanIso m₁ m₂ r r₁ r₂ h₁ h₂).hom =
      (pullbackComparison B S hS r (D.relativeMap m₁.base) r₁ h₁ A₁.F).hom ≫
        (modulePullback B S hS r).map m₁.fibre ≫
        (modulePullback B S hS r).map (inv m₂.fibre) ≫
        (pullbackComparison B S hS r (D.relativeMap m₂.base) r₂ h₂ A₂.F).inv := by
  simp [spanIso]

/-- **Span isomorphisms compose.** -/
theorem spanIso_trans (m₁ : CoherentHom A A₁) (m₂ : CoherentHom A A₂) (m₃ : CoherentHom A A₃)
    {Z : AlgebraicSpaces B S hS} (r : Z ⟶ D.space A.T) (r₁ : Z ⟶ D.space A₁.T)
    (r₂ : Z ⟶ D.space A₂.T) (r₃ : Z ⟶ D.space A₃.T)
    (h₁ : r ≫ D.relativeMap m₁.base = r₁) (h₂ : r ≫ D.relativeMap m₂.base = r₂)
    (h₃ : r ≫ D.relativeMap m₃.base = r₃) :
    spanIso m₁ m₂ r r₁ r₂ h₁ h₂ ≪≫ spanIso m₂ m₃ r r₂ r₃ h₂ h₃ =
      spanIso m₁ m₃ r r₁ r₃ h₁ h₃ := by
  simp [spanIso, Iso.trans_assoc]

/-- The span isomorphism depends only on the two morphisms and on `r`, not on the proofs. -/
theorem spanIso_congr {m₁ m₁' : CoherentHom A A₁} {m₂ m₂' : CoherentHom A A₂}
    {Z : AlgebraicSpaces B S hS} {r r' : Z ⟶ D.space A.T} (r₁ : Z ⟶ D.space A₁.T)
    (r₂ : Z ⟶ D.space A₂.T) (e₁ : m₁ = m₁') (e₂ : m₂ = m₂') (e : r = r')
    (h₁ : r ≫ D.relativeMap m₁.base = r₁) (h₂ : r ≫ D.relativeMap m₂.base = r₂) :
    spanIso m₁ m₂ r r₁ r₂ h₁ h₂ = spanIso m₁' m₂' r' r₁ r₂ (by subst e₁ e; exact h₁)
      (by subst e₂ e; exact h₂) := by
  subst e₁ e₂ e
  rfl

/-- The span isomorphism of a morphism with itself is the identity. -/
theorem spanIso_refl (m₁ : CoherentHom A A₁) {Z : AlgebraicSpaces B S hS}
    (r : Z ⟶ D.space A.T) (r₁ : Z ⟶ D.space A₁.T) (h₁ : r ≫ D.relativeMap m₁.base = r₁) :
    spanIso m₁ m₁ r r₁ r₁ h₁ h₁ = Iso.refl _ := by
  simp [spanIso]

/-- The comparison of Stacks 03LU at a factorization is natural in the module, as an equation of
isomorphisms. -/
theorem pullbackComparison_mapIso {A₀ P T : AlgebraicSpaces B S hS} (w : T ⟶ P) (p : P ⟶ A₀)
    (x : T ⟶ A₀) (hx : w ≫ p = x) {M N : Modules.{u, u} B S hS A₀.1 A₀.2} (e : M ≅ N) :
    pullbackComparison B S hS w p x hx M ≪≫
        (modulePullback B S hS w).mapIso ((modulePullback B S hS p).mapIso e) =
      (modulePullback B S hS x).mapIso e ≪≫ pullbackComparison B S hS w p x hx N := by
  apply Iso.ext
  exact (pullbackComparison_naturality B S hS w p x hx e.hom).symm

/-- The comparison of Stacks 03LU at a composite factorization, applied to the inverse image of an
isomorphism `e`, is the comparison at the two-step factorization, composed with the inverse image
of `e` along the composite. -/
private theorem pullbackComparison_comp_mapIso {X' X₀ X₁ Z : AlgebraicSpaces B S hS}
    {F₀ : Modules.{u, u} B S hS X₀.1 X₀.2} {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2}
    (r : Z ⟶ X') (n : X' ⟶ X₀) (k : X₀ ⟶ X₁) (k' : X' ⟶ X₁) (hk : n ≫ k = k') (rx : Z ⟶ X₁)
    (h : r ≫ k' = rx) (h' : (r ≫ n) ≫ k = rx) (e : (modulePullback B S hS k).obj F₁ ≅ F₀) :
    pullbackComparison B S hS r k' rx h F₁ ≪≫
        (modulePullback B S hS r).mapIso (pullbackComparison B S hS n k k' hk F₁) ≪≫
        (modulePullback B S hS r).mapIso ((modulePullback B S hS n).mapIso e) =
      pullbackComparison B S hS (r ≫ n) k rx h' F₁ ≪≫
        (modulePullback B S hS (r ≫ n)).mapIso e ≪≫
        pullbackComparison B S hS r n (r ≫ n) rfl F₀ := by
  rw [← Iso.trans_assoc,
    pullbackComparison_trans B S hS r n k k' hk (r ≫ n) rfl rx h h' F₁, Iso.trans_assoc,
    pullbackComparison_mapIso r n (r ≫ n) rfl e]

/-- **Span isomorphisms are compatible with inverse image.**  The inverse image along
`s : Z' ⟶ Z` of the span isomorphism along `r`, read through the comparisons of Stacks 03LU, is
the span isomorphism along `s ≫ r`. -/
theorem spanIso_pullback (m₁ : CoherentHom A A₁) (m₂ : CoherentHom A A₂)
    {Z Z' : AlgebraicSpaces B S hS} (r : Z ⟶ D.space A.T) (r₁ : Z ⟶ D.space A₁.T)
    (r₂ : Z ⟶ D.space A₂.T) (h₁ : r ≫ D.relativeMap m₁.base = r₁)
    (h₂ : r ≫ D.relativeMap m₂.base = r₂) (s : Z' ⟶ Z) (r₁' : Z' ⟶ D.space A₁.T)
    (r₂' : Z' ⟶ D.space A₂.T) (hs₁ : s ≫ r₁ = r₁') (hs₂ : s ≫ r₂ = r₂') :
    pullbackComparison B S hS s r₁ r₁' hs₁ A₁.F ≪≫
        (modulePullback B S hS s).mapIso (spanIso m₁ m₂ r r₁ r₂ h₁ h₂) ≪≫
        (pullbackComparison B S hS s r₂ r₂' hs₂ A₂.F).symm =
      spanIso m₁ m₂ (s ≫ r) r₁' r₂' (by rw [Category.assoc, h₁, hs₁])
        (by rw [Category.assoc, h₂, hs₂]) := by
  have x₁ := pullbackComparison_comp_mapIso s r (D.relativeMap m₁.base) r₁ h₁ r₁' hs₁
    (by rw [Category.assoc, h₁, hs₁]) (asIso m₁.fibre)
  have x₂ := pullbackComparison_comp_mapIso s r (D.relativeMap m₂.base) r₂ h₂ r₂' hs₂
    (by rw [Category.assoc, h₂, hs₂]) (asIso m₂.fibre)
  have := congrArg₂ (fun a b => a ≪≫ b.symm) x₁ x₂
  simpa [spanIso, Iso.trans_assoc] using this

/-- The module comparison of a composite of morphisms of `Coh_{X/Y}`, as an isomorphism. -/
theorem asIso_comp_fibre {A' : CoherentObject D} (n : CoherentHom A' A) (m : CoherentHom A A₁) :
    asIso (n.comp m).fibre =
      (D.compComparison n.base m.base).app A₁.F ≪≫
        (modulePullback B S hS (D.relativeMap n.base)).mapIso (asIso m.fibre) ≪≫
        asIso n.fibre := by
  apply Iso.ext
  simp [CoherentHom.comp, Functor.fibreComp]

end CoherentHom

/-- **The span isomorphism of two module comparisons along two morphisms.**  The form of
`AlgebraicGeometry.Space.CoherentHom.spanIso` with the induced morphisms of base changes and the
module comparisons as arguments, which is what lets a law about precomposition be stated with no
projection out of a composite of morphisms of `Coh_{X/Y}`. -/
def spanIsoOf {X₀ X₁ X₂ Z : AlgebraicSpaces B S hS} {F₀ : Modules.{u, u} B S hS X₀.1 X₀.2}
    {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2} {F₂ : Modules.{u, u} B S hS X₂.1 X₂.2}
    (k₁ : X₀ ⟶ X₁) (k₂ : X₀ ⟶ X₂) (e₁ : (modulePullback B S hS k₁).obj F₁ ≅ F₀)
    (e₂ : (modulePullback B S hS k₂).obj F₂ ≅ F₀) (r : Z ⟶ X₀) (r₁ : Z ⟶ X₁) (r₂ : Z ⟶ X₂)
    (h₁ : r ≫ k₁ = r₁) (h₂ : r ≫ k₂ = r₂) :
    (modulePullback B S hS r₁).obj F₁ ≅ (modulePullback B S hS r₂).obj F₂ :=
  pullbackComparison B S hS r k₁ r₁ h₁ F₁ ≪≫ (modulePullback B S hS r).mapIso e₁ ≪≫
    (modulePullback B S hS r).mapIso e₂.symm ≪≫ (pullbackComparison B S hS r k₂ r₂ h₂ F₂).symm

/-- The span isomorphism of two morphisms of `Coh_{X/Y}` is the span isomorphism of their module
comparisons. -/
theorem CoherentHom.spanIso_eq_spanIsoOf {D : CoherentSituation B S hS}
    {A A₁ A₂ : CoherentObject D} (m₁ : CoherentHom A A₁) (m₂ : CoherentHom A A₂)
    {Z : AlgebraicSpaces B S hS} (r : Z ⟶ D.space A.T) (r₁ : Z ⟶ D.space A₁.T)
    (r₂ : Z ⟶ D.space A₂.T) (h₁ : r ≫ D.relativeMap m₁.base = r₁)
    (h₂ : r ≫ D.relativeMap m₂.base = r₂) :
    CoherentHom.spanIso m₁ m₂ r r₁ r₂ h₁ h₂ =
      spanIsoOf (D.relativeMap m₁.base) (D.relativeMap m₂.base) (asIso m₁.fibre)
        (asIso m₂.fibre) r r₁ r₂ h₁ h₂ := by
  simp [CoherentHom.spanIso, spanIsoOf]

/-- **The span isomorphism of two module comparisons, under precomposition.**  If the morphisms
`k₁'`, `k₂'` factor as `n ≫ k₁`, `n ≫ k₂` and the module comparisons `e₁'`, `e₂'` are the
composites of the comparisons of Stacks 03LU, the inverse images along `n` of `e₁`, `e₂`, and one
common isomorphism `e`, then the span isomorphism of `e₁'`, `e₂'` along `r'` is the span
isomorphism of `e₁`, `e₂` along `r' ≫ n`. -/
theorem spanIsoOf_comp {X' X₀ X₁ X₂ Z : AlgebraicSpaces B S hS}
    {F' : Modules.{u, u} B S hS X'.1 X'.2} {F₀ : Modules.{u, u} B S hS X₀.1 X₀.2}
    {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2} {F₂ : Modules.{u, u} B S hS X₂.1 X₂.2}
    (n : X' ⟶ X₀) (e : (modulePullback B S hS n).obj F₀ ≅ F')
    (k₁ : X₀ ⟶ X₁) (k₂ : X₀ ⟶ X₂) (e₁ : (modulePullback B S hS k₁).obj F₁ ≅ F₀)
    (e₂ : (modulePullback B S hS k₂).obj F₂ ≅ F₀) (k₁' : X' ⟶ X₁) (k₂' : X' ⟶ X₂)
    (hk₁ : n ≫ k₁ = k₁') (hk₂ : n ≫ k₂ = k₂')
    (e₁' : (modulePullback B S hS k₁').obj F₁ ≅ F') (e₂' : (modulePullback B S hS k₂').obj F₂ ≅ F')
    (he₁ : e₁' = pullbackComparison B S hS n k₁ k₁' hk₁ F₁ ≪≫
      (modulePullback B S hS n).mapIso e₁ ≪≫ e)
    (he₂ : e₂' = pullbackComparison B S hS n k₂ k₂' hk₂ F₂ ≪≫
      (modulePullback B S hS n).mapIso e₂ ≪≫ e)
    (r' : Z ⟶ X') (r₁ : Z ⟶ X₁) (r₂ : Z ⟶ X₂) (h₁ : r' ≫ k₁' = r₁) (h₂ : r' ≫ k₂' = r₂)
    (h₁' : (r' ≫ n) ≫ k₁ = r₁) (h₂' : (r' ≫ n) ≫ k₂ = r₂) :
    spanIsoOf k₁' k₂' e₁' e₂' r' r₁ r₂ h₁ h₂ = spanIsoOf k₁ k₂ e₁ e₂ (r' ≫ n) r₁ r₂ h₁' h₂' := by
  subst he₁ he₂
  have x₁ := CoherentHom.pullbackComparison_comp_mapIso r' n k₁ k₁' hk₁ r₁ h₁ h₁' e₁
  have x₂ := CoherentHom.pullbackComparison_comp_mapIso r' n k₂ k₂' hk₂ r₂ h₂ h₂' e₂
  have := congrArg₂ (fun a b => a ≪≫ b.symm) x₁ x₂
  simpa [spanIsoOf, Iso.trans_assoc] using this

/-- **The reading of a module comparison along a morphism.**  For `k : X₀ ⟶ X₁`, an
isomorphism `e : k^*F₁ ≅ F₀` and `r : Z ⟶ X₀` with composite `r'`, the isomorphism
`r'^*F₁ ≅ r^*F₀` of the comparison of Stacks 03LU at `r ≫ k = r'` followed by the inverse image of
`e`. -/
def readOf {X₀ X₁ Z : AlgebraicSpaces B S hS} {F₀ : Modules.{u, u} B S hS X₀.1 X₀.2}
    {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2} (k : X₀ ⟶ X₁)
    (e : (modulePullback B S hS k).obj F₁ ≅ F₀) (r : Z ⟶ X₀) (r' : Z ⟶ X₁) (h : r ≫ k = r') :
    (modulePullback B S hS r').obj F₁ ≅ (modulePullback B S hS r).obj F₀ :=
  pullbackComparison B S hS r k r' h F₁ ≪≫ (modulePullback B S hS r).mapIso e

/-- A span isomorphism is a reading followed by the inverse of a reading. -/
theorem spanIsoOf_eq_readOf {X₀ X₁ X₂ Z : AlgebraicSpaces B S hS}
    {F₀ : Modules.{u, u} B S hS X₀.1 X₀.2} {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2}
    {F₂ : Modules.{u, u} B S hS X₂.1 X₂.2} (k₁ : X₀ ⟶ X₁) (k₂ : X₀ ⟶ X₂)
    (e₁ : (modulePullback B S hS k₁).obj F₁ ≅ F₀) (e₂ : (modulePullback B S hS k₂).obj F₂ ≅ F₀)
    (r : Z ⟶ X₀) (r₁ : Z ⟶ X₁) (r₂ : Z ⟶ X₂) (h₁ : r ≫ k₁ = r₁) (h₂ : r ≫ k₂ = r₂) :
    spanIsoOf k₁ k₂ e₁ e₂ r r₁ r₂ h₁ h₂ = readOf k₁ e₁ r r₁ h₁ ≪≫ (readOf k₂ e₂ r r₂ h₂).symm := by
  simp [spanIsoOf, readOf, Iso.trans_assoc]

/-- **The reading of a composite comparison is the composite of the readings.** -/
theorem readOf_comp {X' X₀ X₁ Z : AlgebraicSpaces B S hS}
    {F' : Modules.{u, u} B S hS X'.1 X'.2} {F₀ : Modules.{u, u} B S hS X₀.1 X₀.2}
    {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2} (n : X' ⟶ X₀) (e : (modulePullback B S hS n).obj F₀ ≅ F')
    (k : X₀ ⟶ X₁) (e₁ : (modulePullback B S hS k).obj F₁ ≅ F₀) (k' : X' ⟶ X₁)
    (hk : n ≫ k = k') (e' : (modulePullback B S hS k').obj F₁ ≅ F')
    (he : e' = pullbackComparison B S hS n k k' hk F₁ ≪≫ (modulePullback B S hS n).mapIso e₁ ≪≫ e)
    (r : Z ⟶ X') (r₀ : Z ⟶ X₀) (h₀ : r ≫ n = r₀) (rx : Z ⟶ X₁) (h : r ≫ k' = rx)
    (h' : r₀ ≫ k = rx) :
    readOf k' e' r rx h = readOf k e₁ r₀ rx h' ≪≫ readOf n e r r₀ h₀ := by
  subst he h₀
  have x := CoherentHom.pullbackComparison_comp_mapIso r n k k' hk rx h h' e₁
  simp only [readOf, Functor.mapIso_trans, Iso.trans_assoc]
  rw [← Iso.trans_assoc _ _ ((modulePullback B S hS r).mapIso e), ← Iso.trans_assoc, x,
    Iso.trans_assoc, Iso.trans_assoc]

/-- **The span isomorphism of two composite comparisons through a cocone is the identity.**  Let
`c' : X_Q ⟶ X₁`, `e' : X_Q ⟶ X₂` carry module comparisons `εc`, `εe` with a module `F_Q`, and let
`a₁ : X₁ ⟶ X₀`, `a₂ : X₂ ⟶ X₀` carry module comparisons `ζ₁`, `ζ₂` of the modules of `X₁`, `X₂`
with the inverse images of one module `M` on `X₀`.  If along `r : Z ⟶ X_Q`, with composites `p₁`,
`p₂` and common composite `rx` to `X₀`, the span isomorphism `τ` of `εc` and `εe` is intertwined by
the inverse images of `ζ₁`, `ζ₂` with the canonical comparison of the two inverse images of `M`,
then the span isomorphism along `r` of the two composite comparisons
`(c' ≫ a₁)^*M ≅ F_Q` and `(e' ≫ a₂)^*M ≅ F_Q` is the identity. -/
theorem spanIsoOf_comp_eq_refl {Z X_Q X₁ X₂ X₀ : AlgebraicSpaces B S hS}
    {F_Q : Modules.{u, u} B S hS X_Q.1 X_Q.2} {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2}
    {F₂ : Modules.{u, u} B S hS X₂.1 X₂.2} {M : Modules.{u, u} B S hS X₀.1 X₀.2}
    (c' : X_Q ⟶ X₁) (e' : X_Q ⟶ X₂) (εc : (modulePullback B S hS c').obj F₁ ≅ F_Q)
    (εe : (modulePullback B S hS e').obj F₂ ≅ F_Q) (a₁ : X₁ ⟶ X₀) (a₂ : X₂ ⟶ X₀)
    (ζ₁ : (modulePullback B S hS a₁).obj M ≅ F₁) (ζ₂ : (modulePullback B S hS a₂).obj M ≅ F₂)
    (k₁ k₂ : X_Q ⟶ X₀) (hk₁ : c' ≫ a₁ = k₁) (hk₂ : e' ≫ a₂ = k₂)
    (κ₁ : (modulePullback B S hS k₁).obj M ≅ F_Q) (κ₂ : (modulePullback B S hS k₂).obj M ≅ F_Q)
    (hκ₁ : κ₁ = pullbackComparison B S hS c' a₁ k₁ hk₁ M ≪≫
      (modulePullback B S hS c').mapIso ζ₁ ≪≫ εc)
    (hκ₂ : κ₂ = pullbackComparison B S hS e' a₂ k₂ hk₂ M ≪≫
      (modulePullback B S hS e').mapIso ζ₂ ≪≫ εe)
    (r : Z ⟶ X_Q) (p₁ : Z ⟶ X₁) (p₂ : Z ⟶ X₂) (hp₁ : r ≫ c' = p₁) (hp₂ : r ≫ e' = p₂)
    (rx : Z ⟶ X₀) (hx₁ : p₁ ≫ a₁ = rx) (hx₂ : p₂ ≫ a₂ = rx)
    (h₁ : r ≫ k₁ = rx) (h₂ : r ≫ k₂ = rx)
    (hnat : (modulePullback B S hS p₁).mapIso ζ₁.symm ≪≫
        ((pullbackComparison B S hS p₁ a₁ rx hx₁ M).symm ≪≫
          pullbackComparison B S hS p₂ a₂ rx hx₂ M) =
      spanIsoOf c' e' εc εe r p₁ p₂ hp₁ hp₂ ≪≫ (modulePullback B S hS p₂).mapIso ζ₂.symm) :
    spanIsoOf k₁ k₂ κ₁ κ₂ r rx rx h₁ h₂ = Iso.refl _ := by
  rw [spanIsoOf_eq_readOf,
    readOf_comp c' εc a₁ ζ₁ k₁ hk₁ κ₁ hκ₁ r p₁ hp₁ rx h₁ hx₁,
    readOf_comp e' εe a₂ ζ₂ k₂ hk₂ κ₂ hκ₂ r p₂ hp₂ rx h₂ hx₂]
  have hτ : readOf c' εc r p₁ hp₁ ≪≫ (readOf e' εe r p₂ hp₂).symm =
      spanIsoOf c' e' εc εe r p₁ p₂ hp₁ hp₂ := (spanIsoOf_eq_readOf _ _ _ _ _ _ _ _ _).symm
  have hτ' : spanIsoOf c' e' εc εe r p₁ p₂ hp₁ hp₂ =
      (modulePullback B S hS p₁).mapIso ζ₁.symm ≪≫
        ((pullbackComparison B S hS p₁ a₁ rx hx₁ M).symm ≪≫
          pullbackComparison B S hS p₂ a₂ rx hx₂ M) ≪≫
        ((modulePullback B S hS p₂).mapIso ζ₂.symm).symm := by
    rw [← Iso.trans_assoc, hnat, Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl]
  calc
    _ = readOf a₁ ζ₁ p₁ rx hx₁ ≪≫ (readOf c' εc r p₁ hp₁ ≪≫ (readOf e' εe r p₂ hp₂).symm) ≪≫
          (readOf a₂ ζ₂ p₂ rx hx₂).symm := by
      simp only [Iso.trans_symm, Iso.trans_assoc]
    _ = _ := by
      rw [hτ, hτ']
      apply Iso.ext
      simp [readOf, Iso.trans_assoc]

/-- **The inverse image along an isomorphism of algebraic spaces is faithful.**  Followed by the
inverse image along the inverse, it is the inverse image along an identity, which is the identity
functor. -/
theorem faithful_modulePullback_of_isIso {Z X₀ : AlgebraicSpaces B S hS} (r : Z ⟶ X₀) [IsIso r] :
    (modulePullback B S hS r).Faithful :=
  Functor.Faithful.of_comp_iso (G := modulePullback B S hS (inv r))
    (modulePullbackCompIso B S hS (inv r) r ≪≫
      eqToIso (congrArg (modulePullback B S hS) (IsIso.inv_hom_id r)) ≪≫
      modulePullbackIdIso B S hS X₀)

namespace CoherentHom

variable {D : CoherentSituation B S hS} {A A₁ A₂ : CoherentObject D}

/-- **Span isomorphisms are unchanged by precomposition.**  The span isomorphism of `n ≫ m₁` and
`n ≫ m₂` along `r'` is the span isomorphism of `m₁` and `m₂` along `r' ≫ X_n`. -/
theorem spanIso_comp {A' : CoherentObject D} (n : CoherentHom A' A) (m₁ : CoherentHom A A₁)
    (m₂ : CoherentHom A A₂) {Z : AlgebraicSpaces B S hS} (r' : Z ⟶ D.space A'.T)
    (r₁ : Z ⟶ D.space A₁.T) (r₂ : Z ⟶ D.space A₂.T)
    (h₁ : r' ≫ D.relativeMap (n.comp m₁).base = r₁)
    (h₂ : r' ≫ D.relativeMap (n.comp m₂).base = r₂)
    (h₁' : (r' ≫ D.relativeMap n.base) ≫ D.relativeMap m₁.base = r₁)
    (h₂' : (r' ≫ D.relativeMap n.base) ≫ D.relativeMap m₂.base = r₂) :
    spanIso (n.comp m₁) (n.comp m₂) r' r₁ r₂ h₁ h₂ =
      spanIso m₁ m₂ (r' ≫ D.relativeMap n.base) r₁ r₂ h₁' h₂' := by
  rw [spanIso_eq_spanIsoOf, spanIso_eq_spanIsoOf]
  refine spanIsoOf_comp (D.relativeMap n.base) (asIso n.fibre) (D.relativeMap m₁.base)
    (D.relativeMap m₂.base) (asIso m₁.fibre) (asIso m₂.fibre) _ _
    (baseChangeMap_comp D.f n.base m₁.base).symm (baseChangeMap_comp D.f n.base m₂.base).symm
    _ _ ?_ ?_ r' r₁ r₂ h₁ h₂ h₁' h₂'
  · rw [asIso_comp_fibre, D.compComparison_app]
  · rw [asIso_comp_fibre, D.compComparison_app]

end CoherentHom

/-- An isomorphism conjugated to the identity by another isomorphism, after composition with the
inverse of a third, is that third.  Stated in an arbitrary category so that it is instantiated,
never re-proved, at the modules on an algebraic space. -/
theorem _root_.CategoryTheory.Iso.eq_of_conj_trans_symm_eq_refl {C : Type*} [Category C]
    {X Y Z : C} (p : X ≅ Y) (u v : Y ≅ Z) (h : p ≪≫ u ≪≫ v.symm ≪≫ p.symm = Iso.refl X) :
    u = v := by
  have h' := congrArg (fun z => p.symm ≪≫ z ≪≫ p ≪≫ v) h
  simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.self_symm_id_assoc,
    Iso.symm_self_id, Iso.trans_refl, Iso.refl_trans] using h'

/-- **Two morphisms of `Coh_{X/Y}` with the same base map are equal as soon as their span
isomorphism along an isomorphism onto the base change of their source is the identity.** -/
theorem CoherentHom.eq_of_spanIso_eq_refl {D : CoherentSituation B S hS} {A A' : CoherentObject D}
    (n₁ n₂ : CoherentHom A A') (hb : n₁.base = n₂.base) {Z : AlgebraicSpaces B S hS}
    (r : Z ⟶ D.space A.T) [IsIso r] (rx : Z ⟶ D.space A'.T)
    (h₁ : r ≫ D.relativeMap n₁.base = rx) (h₂ : r ≫ D.relativeMap n₂.base = rx)
    (h : CoherentHom.spanIso n₁ n₂ r rx rx h₁ h₂ = Iso.refl _) : n₁ = n₂ := by
  obtain ⟨b₁, f₁, i₁⟩ := n₁
  obtain ⟨b₂, f₂, i₂⟩ := n₂
  change b₁ = b₂ at hb
  subst hb
  have hu := Iso.eq_of_conj_trans_symm_eq_refl
    (pullbackComparison B S hS r (D.relativeMap b₁) rx h₁ A'.F)
    ((modulePullback B S hS r).mapIso (asIso f₁)) ((modulePullback B S hS r).mapIso (asIso f₂))
    h
  have hf : (modulePullback B S hS r).map f₁ = (modulePullback B S hS r).map f₂ :=
    congrArg Iso.hom hu
  have hfa := faithful_modulePullback_of_isIso r
  have hff : f₁ = f₂ := hfa.map_injective hf
  subst hff
  rfl

end AlgebraicGeometry.Space

end
