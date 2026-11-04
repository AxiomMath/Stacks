module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackObjCmp
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackObjCovering

/-!
# The local identifications of a candidate object, and when they glue

`AlgebraicGeometry.BigHOver.nonempty_descentSolution_of_covering` turns an object `y` of the fibre
over `W`, identified over each member of an h covering of `W` with the object of a solution of a
descent problem there, into a solution over `W` itself — provided the resulting local comparisons
do not depend on which member of the covering they are read through. This file factors that
hypothesis.

The local comparison is the composite of two things: an identification of the chosen pullback of
`y` with the object of the local solution (`AlgebraicGeometry.BigHOver.localIso`), and the
identification that solution already carries. Only the first depends on the member of the covering,
so the hypothesis of the gluing is an identity between the two readings of the first, and that
identity says exactly that the two readings differ by the *canonical* comparison of the two local
solutions, `AlgebraicGeometry.BigHOver.DescentSolution.cmpIso`. That is the form
`AlgebraicGeometry.BigHOver.nonempty_descentSolution_of_glueCmp` takes.

## Main definitions

* `AlgebraicGeometry.BigHOver.localIso`: the local identification of `y` with the object of a
  solution over a member of the covering, read over an arbitrary object mapping to that member.
* `AlgebraicGeometry.BigHOver.glueCmpMor`: the comparison of two local identifications, which is
  the morphism the gluing hypothesis asks to be the canonical comparison.

## Main results

* `AlgebraicGeometry.BigHOver.localIso_hom_baseChange` and
  `AlgebraicGeometry.BigHOver.localIso_inv_baseChange`: the local identifications are compatible
  with base change, hence so is `AlgebraicGeometry.BigHOver.glueCmpMor_baseChange`.
* `AlgebraicGeometry.BigHOver.glueCmpMor_self` and
  `AlgebraicGeometry.BigHOver.glueCmpMor_trans`: the comparisons of local identifications are a
  transitive system.
* `AlgebraicGeometry.BigHOver.nonempty_descentSolution_of_glueCmp`: the gluing, with the
  independence hypothesis replaced by the statement that each comparison of local identifications
  is the canonical comparison of the two local solutions.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t v u

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : Type t} [Category.{v} 𝒳] {p : 𝒳 ⥤ BigHOver B S hS} [p.IsFibered]

/-! ### The local identifications -/

/-- **The local identification of `y` with the object of a solution over a member of a covering.**
Given a morphism `g : Wd ⟶ W`, an object `y` of the fibre over `W` and an identification `β` of its
chosen pullback along `g` with an object `o` of the fibre over `Wd`, every morphism `ε : T ⟶ Wd`
over a named composite `r = ε ≫ g` identifies the chosen pullback of `y` along `r` with the chosen
pullback of `o` along `ε`: contract the iterated chosen pullback of `y` and apply `β`. -/
public def localIso {W Wd : BigHOver B S hS} {y : p.Fiber W} {o : p.Fiber Wd} (g : Wd ⟶ W)
    (β : Functor.pullbackFiber p y g ≅ o) {T : BigHOver B S hS} (ε : T ⟶ Wd) (r : T ⟶ W)
    (hr : ε ≫ g = r) :
    Functor.pullbackFiber p y r ≅ Functor.pullbackFiber p o ε where
  hom := (Functor.pullbackFiberCompIso' y g ε r hr).inv ≫ Functor.pullbackFiberHom β.hom ε
  inv := Functor.pullbackFiberHom β.inv ε ≫ (Functor.pullbackFiberCompIso' y g ε r hr).hom
  hom_inv_id := by
    simp only [Category.assoc]
    rw [← Category.assoc (Functor.pullbackFiberHom β.hom ε), ← Functor.pullbackFiberHom_comp,
      β.hom_inv_id, Functor.pullbackFiberHom_id, Category.id_comp, Iso.inv_hom_id]
  inv_hom_id := by
    simp only [Category.assoc]
    rw [Iso.hom_inv_id_assoc, ← Functor.pullbackFiberHom_comp, β.inv_hom_id,
      Functor.pullbackFiberHom_id]

/-- The forward direction of `AlgebraicGeometry.BigHOver.localIso`. -/
public theorem localIso_hom {W Wd : BigHOver B S hS} {y : p.Fiber W} {o : p.Fiber Wd} (g : Wd ⟶ W)
    (β : Functor.pullbackFiber p y g ≅ o) {T : BigHOver B S hS} (ε : T ⟶ Wd) (r : T ⟶ W)
    (hr : ε ≫ g = r) :
    (localIso g β ε r hr).hom =
      (Functor.pullbackFiberCompIso' y g ε r hr).inv ≫ Functor.pullbackFiberHom β.hom ε := rfl

/-- The inverse direction of `AlgebraicGeometry.BigHOver.localIso`. -/
public theorem localIso_inv {W Wd : BigHOver B S hS} {y : p.Fiber W} {o : p.Fiber Wd} (g : Wd ⟶ W)
    (β : Functor.pullbackFiber p y g ≅ o) {T : BigHOver B S hS} (ε : T ⟶ Wd) (r : T ⟶ W)
    (hr : ε ≫ g = r) :
    (localIso g β ε r hr).inv =
      Functor.pullbackFiberHom β.inv ε ≫ (Functor.pullbackFiberCompIso' y g ε r hr).hom := rfl

/-- **The local identifications are compatible with base change.** -/
public theorem localIso_hom_baseChange {W Wd : BigHOver B S hS} {y : p.Fiber W} {o : p.Fiber Wd}
    (g : Wd ⟶ W) (β : Functor.pullbackFiber p y g ≅ o) {T T' : BigHOver B S hS} (ε : T ⟶ Wd)
    (r : T ⟶ W) (hr : ε ≫ g = r) (μ : T' ⟶ T) (δ : T' ⟶ Wd) (hδ : μ ≫ ε = δ) (r' : T' ⟶ W)
    (hrr : μ ≫ r = r') (hd : δ ≫ g = r') :
    Functor.baseChangeFiberMor (localIso g β ε r hr).hom μ r' hrr δ hδ =
      (localIso g β δ r' hd).hom := by
  rw [localIso_hom, localIso_hom, Functor.baseChangeFiberMor_comp _ _ μ r' hrr δ hδ δ hδ,
    baseChangeFiberMor_pullbackFiberCompIso'_inv y g ε r hr μ δ hδ r' hd hrr,
    ← Functor.pullbackFiberHom_eq_baseChangeFiberMor β.hom ε μ δ hδ]

/-- **The inverse local identifications are compatible with base change.** -/
public theorem localIso_inv_baseChange {W Wd : BigHOver B S hS} {y : p.Fiber W} {o : p.Fiber Wd}
    (g : Wd ⟶ W) (β : Functor.pullbackFiber p y g ≅ o) {T T' : BigHOver B S hS} (ε : T ⟶ Wd)
    (r : T ⟶ W) (hr : ε ≫ g = r) (μ : T' ⟶ T) (δ : T' ⟶ Wd) (hδ : μ ≫ ε = δ) (r' : T' ⟶ W)
    (hrr : μ ≫ r = r') (hd : δ ≫ g = r') :
    Functor.baseChangeFiberMor (localIso g β ε r hr).inv μ δ hδ r' hrr =
      (localIso g β δ r' hd).inv := by
  rw [localIso_inv, localIso_inv, Functor.baseChangeFiberMor_comp _ _ μ δ hδ δ hδ r' hrr,
    ← Functor.pullbackFiberHom_eq_baseChangeFiberMor β.inv ε μ δ hδ,
    Functor.baseChangeFiberMor_pullbackFiberCompIso' y g ε r hr μ δ hδ r' hd hrr]

/-! ### The comparison of two local identifications -/

/-- **The comparison of two local identifications of `y`.** Over an object mapping to two members
of the covering compatibly over `W`, the two local identifications differ by this morphism between
the chosen pullbacks of the two local objects. -/
public def glueCmpMor {W Wd Wd' : BigHOver B S hS} {y : p.Fiber W} {o : p.Fiber Wd}
    {o' : p.Fiber Wd'} (g : Wd ⟶ W) (β : Functor.pullbackFiber p y g ≅ o)
    {T : BigHOver B S hS} (ε : T ⟶ Wd) (g' : Wd' ⟶ W)
    (β' : Functor.pullbackFiber p y g' ≅ o') (ε' : T ⟶ Wd') (r : T ⟶ W) (hr : ε ≫ g = r)
    (hr' : ε' ≫ g' = r) :
    Functor.pullbackFiber p o ε ⟶ Functor.pullbackFiber p o' ε' :=
  (localIso g β ε r hr).inv ≫ (localIso g' β' ε' r hr').hom

/-- `AlgebraicGeometry.BigHOver.glueCmpMor` unfolded. -/
public theorem glueCmpMor_eq {W Wd Wd' : BigHOver B S hS} {y : p.Fiber W} {o : p.Fiber Wd}
    {o' : p.Fiber Wd'} (g : Wd ⟶ W) (β : Functor.pullbackFiber p y g ≅ o)
    {T : BigHOver B S hS} (ε : T ⟶ Wd) (g' : Wd' ⟶ W)
    (β' : Functor.pullbackFiber p y g' ≅ o') (ε' : T ⟶ Wd') (r : T ⟶ W) (hr : ε ≫ g = r)
    (hr' : ε' ≫ g' = r) :
    glueCmpMor g β ε g' β' ε' r hr hr' =
      (localIso g β ε r hr).inv ≫ (localIso g' β' ε' r hr').hom := rfl

/-- A local identification is compared with itself by the identity. -/
public theorem glueCmpMor_self {W Wd : BigHOver B S hS} {y : p.Fiber W} {o : p.Fiber Wd}
    (g : Wd ⟶ W) (β : Functor.pullbackFiber p y g ≅ o) {T : BigHOver B S hS} (ε : T ⟶ Wd)
    (r : T ⟶ W) (hr hr' : ε ≫ g = r) : glueCmpMor g β ε g β ε r hr hr' = 𝟙 _ := by
  obtain rfl : hr = hr' := rfl
  exact (localIso g β ε r hr).inv_hom_id

/-- The comparisons of three local identifications compose. -/
public theorem glueCmpMor_trans {W Wd Wd' Wd'' : BigHOver B S hS} {y : p.Fiber W}
    {o : p.Fiber Wd} {o' : p.Fiber Wd'} {o'' : p.Fiber Wd''} (g : Wd ⟶ W)
    (β : Functor.pullbackFiber p y g ≅ o) {T : BigHOver B S hS} (ε : T ⟶ Wd) (g' : Wd' ⟶ W)
    (β' : Functor.pullbackFiber p y g' ≅ o') (ε' : T ⟶ Wd') (g'' : Wd'' ⟶ W)
    (β'' : Functor.pullbackFiber p y g'' ≅ o'') (ε'' : T ⟶ Wd'') (r : T ⟶ W) (hr : ε ≫ g = r)
    (hr' : ε' ≫ g' = r) (hr'' : ε'' ≫ g'' = r) :
    glueCmpMor g β ε g' β' ε' r hr hr' ≫ glueCmpMor g' β' ε' g'' β'' ε'' r hr' hr'' =
      glueCmpMor g β ε g'' β'' ε'' r hr hr'' := by
  simp only [glueCmpMor, Category.assoc, Iso.hom_inv_id_assoc]

/-- **The comparisons of local identifications are compatible with base change.** -/
public theorem glueCmpMor_baseChange {W Wd Wd' : BigHOver B S hS} {y : p.Fiber W}
    {o : p.Fiber Wd} {o' : p.Fiber Wd'} (g : Wd ⟶ W) (β : Functor.pullbackFiber p y g ≅ o)
    {T T' : BigHOver B S hS} (ε : T ⟶ Wd) (g' : Wd' ⟶ W)
    (β' : Functor.pullbackFiber p y g' ≅ o') (ε' : T ⟶ Wd') (r : T ⟶ W) (hr : ε ≫ g = r)
    (hr' : ε' ≫ g' = r) (μ : T' ⟶ T) (δ : T' ⟶ Wd) (hδ : μ ≫ ε = δ) (δ' : T' ⟶ Wd')
    (hδ' : μ ≫ ε' = δ') (r' : T' ⟶ W) (hrr : μ ≫ r = r') (hd : δ ≫ g = r') (hd' : δ' ≫ g' = r') :
    Functor.baseChangeFiberMor (glueCmpMor g β ε g' β' ε' r hr hr') μ δ hδ δ' hδ' =
      glueCmpMor g β δ g' β' δ' r' hd hd' := by
  rw [glueCmpMor, glueCmpMor, Functor.baseChangeFiberMor_comp _ _ μ δ hδ r' hrr δ' hδ',
    localIso_inv_baseChange g β ε r hr μ δ hδ r' hrr hd,
    localIso_hom_baseChange g' β' ε' r hr' μ δ' hδ' r' hrr hd']

/-! ### The gluing -/

variable {U : BigHOver B S hS} {I : Type (u + 1)} {V : I → BigHOver B S hS} {f : ∀ i, V i ⟶ U}
variable {D : (Functor.IsFibered.pullbackPseudofunctor p).DescentData f}
variable {W : BigHOver B S hS} {F : W ⟶ U} {K : Type (u + 1)} {Wc : K → BigHOver B S hS}
  {γ : ∀ c, Wc c ⟶ W} {Fc : ∀ c, Wc c ⟶ U}

/-- The local comparison of
`AlgebraicGeometry.BigHOver.DescentSolution.glueLocalMor` read through
`AlgebraicGeometry.BigHOver.localIso`: it is the local identification followed by the
identification the local solution carries. -/
public theorem glueLocalMor_eq_localIso {s : ∀ c, DescentSolution D (Fc c)} {y : p.Fiber W}
    (hFc : ∀ c, γ c ≫ F = Fc c) (β : ∀ c, Functor.pullbackFiber p y (γ c) ≅ (s c).obj) (c : K)
    ⦃T : BigHOver B S hS⦄ (ε : T ⟶ Wc c) (r : T ⟶ W) (hr : ε ≫ γ c = r) (i : I) (ζ : T ⟶ V i)
    (qq : T ⟶ U) (hqq : r ≫ F = qq) (hζ : ζ ≫ f i = qq) (hεq : ε ≫ Fc c = qq) :
    DescentSolution.glueLocalMor hFc β c ε r hr i ζ qq hqq hζ =
      (localIso (γ c) (β c) ε r hr).hom ≫ ((s c).iso i ε ζ qq hεq hζ).hom := by
  rw [DescentSolution.glueLocalMor_eq hFc β c ε r hr i ζ qq hqq hζ hεq, localIso_hom,
    Category.assoc]

/-- **A solution glued from solutions over an h covering of the source, with the independence
hypothesis read as a comparison.** This is
`AlgebraicGeometry.BigHOver.nonempty_descentSolution_of_covering` with its hypothesis replaced by
the statement that each comparison of two local identifications of `y` is *the* canonical
comparison of the two local solutions,
`AlgebraicGeometry.BigHOver.DescentSolution.cmpIso`. -/
public theorem nonempty_descentSolution_of_glueCmp
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hcov : Sieve.ofArrows Wc γ ∈ BigHOver.topology B S hS W)
    {s : ∀ c, DescentSolution D (Fc c)} {y : p.Fiber W} (hFc : ∀ c, γ c ≫ F = Fc c)
    (β : ∀ c, Functor.pullbackFiber p y (γ c) ≅ (s c).obj)
    (hcmp : ∀ (c c' : K) (T : BigHOver B S hS) (ε : T ⟶ Wc c) (ε' : T ⟶ Wc c') (r : T ⟶ W)
      (hr : ε ≫ γ c = r) (hr' : ε' ≫ γ c' = r),
      DescentSolution.IsCmp (s c) ε (s c') ε'
        (glueCmpMor (γ c) (β c) ε (γ c') (β c') ε' r hr hr')) :
    Nonempty (DescentSolution D F) := by
  refine nonempty_descentSolution_of_covering h1 h2 h3 h4 hcov hFc β ?_
  intro c c' T ε ε' r hr hr' i ζ qq hqq hζ
  have hεq : ε ≫ Fc c = qq := by rwa [← hFc c, ← Category.assoc, hr]
  have hεq' : ε' ≫ Fc c' = qq := by rwa [← hFc c', ← Category.assoc, hr']
  rw [glueLocalMor_eq_localIso hFc β c ε r hr i ζ qq hqq hζ hεq,
    glueLocalMor_eq_localIso hFc β c' ε' r hr' i ζ qq hqq hζ hεq']
  have hfac := (hcmp c c' T ε ε' r hr hr').fac i ζ qq hεq hεq' hζ
  rw [glueCmpMor] at hfac
  rw [← hfac]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end BigHOver

end AlgebraicGeometry

end
