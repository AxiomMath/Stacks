module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackObjLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackMorExists
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackDiagonalCovering

/-!
# Existence of a solution of a descent problem over the base

The four locality steps for the property

> the descent problem `D` relative to an h covering family of `U` has a solution over `Y ⟶ U`

of an object `Y` of the slice at `U`, in the form
`AlgebraicGeometry.BigHOver.of_localOnGenerators` consumes them, and the conclusion they give:
`AlgebraicGeometry.BigHOver.nonempty_descentSolution_id`, a solution over `𝟙 U`.

All four steps are
`AlgebraicGeometry.BigHOver.nonempty_descentSolution_of_glueCmp`, and what differs between them is
only where the object of the fibre over the base comes from:

* the Zariski step takes it from effective descent for the Zariski topology, which is condition (1)
  of Stacks 0EX9 read through the bridge
  `CategoryTheory.Functor.isStack_of_isStackInGroupoids` and Stacks 02ZF;
* the three remaining steps take it from essential surjectivity of the comparison functor
  `AlgebraicGeometry.BigHOver.twoFibreProductComparison`, through
  `AlgebraicGeometry.BigHOver.exists_fiberObj`, the isomorphism over the exceptional corner being
  the canonical comparison `AlgebraicGeometry.BigHOver.DescentSolution.cmpIso` of the two local
  solutions.

In the Zariski step the local solutions are glued along the covering family itself, and the
independence hypothesis of the gluing is read off the isomorphism of descent data that effective
descent produces.  In the three remaining steps the covering is the one- or two-element family
attached to the square, and the independence hypothesis has to be checked pair by pair:

* for the self-square of a flat proper finitely-presented surjection the family is the morphism
  itself, and its single pair factors through the exceptional corner `X ×_Y X`;
* for an almost blowup square the family is `{Z ⟶ X, X' ⟶ X}`; the two mixed pairs factor through
  the exceptional corner, the pair `(Z, Z)` is trivial because the centre is a monomorphism
  (`AlgebraicGeometry.BigHOver.mono_center_of_almostBlowUpSquare`), and the pair `(X', X')`
  factors through `X' ×_X X'`, which is covered by the base change of the centre and the diagonal
  (`AlgebraicGeometry.BigHOver.sieve_ofArrows_pair_diagonal_mem_topology`), so that
  `AlgebraicGeometry.BigHOver.DescentSolution.isCmp_of_covering` reduces it to the mixed pairs.

## Main definitions

* `AlgebraicGeometry.BigHOver.solutionDescentData`: the descent datum, for the pullback
  pseudofunctor, assembled out of a family of solutions over a covering, its gluing isomorphisms
  being the canonical comparisons.
* `AlgebraicGeometry.BigHOver.pairSolution` and `AlgebraicGeometry.BigHOver.pairLocalIso`: the
  two-element families of solutions and of local identifications.

## Main results

* `AlgebraicGeometry.BigHOver.exists_glue_of_square`: the object and the identifications a
  cartesian square along which the comparison functor is an equivalence provides, together with
  the mixed-pair comparison.
* `AlgebraicGeometry.BigHOver.nonempty_descentSolution_of_isEquivalence_toDescentData`: gluing
  solutions along an h covering family with effective descent; the steps for a Zariski covering and
  for a flat proper surjection of finite presentation onto an affine object are this, by
  condition (1) and by condition (2) of Stacks 0EX9 in its descent form.
* `AlgebraicGeometry.BigHOver.nonempty_descentSolution_zariski` and
  `AlgebraicGeometry.BigHOver.nonempty_descentSolution_almostBlowUpSquare`: the Zariski step and
  the step for an almost blowup square.
* `AlgebraicGeometry.BigHOver.nonempty_descentSolution_selfSquare`: the same gluing across the
  self-square of a morphism, along which the comparison functor onto the two-fibre product is an
  equivalence; not used by the criterion, whose condition (2) is the descent form.
* `AlgebraicGeometry.BigHOver.nonempty_descentSolution_id`: a solution over `𝟙 U`.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
* [Stacks Project, Tag 02ZF](https://stacks.math.columbia.edu/tag/02ZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t v u

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : Type t} [Category.{v} 𝒳] {p : 𝒳 ⥤ BigHOver B S hS} [p.IsFibered]
variable {U : BigHOver B S hS} {I : Type (u + 1)} {V : I → BigHOver B S hS} {f : ∀ i, V i ⟶ U}
variable {D : (Functor.IsFibered.pullbackPseudofunctor p).DescentData f}

/-! ### Two generic steps in the comparison of local identifications -/

/-- A composite into `U` through a morphism `γ` into `W`, read through `W`. -/
private theorem comp_eq_of_comp_eq {W V' T : BigHOver B S hS} {F : W ⟶ U} {Fc : V' ⟶ U}
    {γ : V' ⟶ W} (h : γ ≫ F = Fc) (ε : T ⟶ V') {q : T ⟶ W} (hε : ε ≫ γ = q) :
    ε ≫ Fc = q ≫ F := by
  rw [← h, ← Category.assoc, hε]

/-- A composite into `U` through a member of a covering of `W`, read through `W`. -/
public theorem comp_eq_of_covering_fac {W : BigHOver B S hS} {F : W ⟶ U} {K : Type (u + 1)}
    {Wc : K → BigHOver B S hS} {γ : ∀ c, Wc c ⟶ W} {Fc : ∀ c, Wc c ⟶ U}
    (hFc : ∀ c, γ c ≫ F = Fc c) (c : K) {T : BigHOver B S hS} (ε : T ⟶ Wc c) (q : T ⟶ W)
    (hε : ε ≫ γ c = q) : ε ≫ Fc c = q ≫ F :=
  comp_eq_of_comp_eq (hFc c) ε hε

/-- The comparison of two local identifications is an isomorphism, being a composite of two
local identifications. -/
public theorem isIso_glueCmpMor {W Wd Wd' : BigHOver B S hS} {y : p.Fiber W} {o : p.Fiber Wd}
    {o' : p.Fiber Wd'} (g : Wd ⟶ W) (β : Functor.pullbackFiber p y g ≅ o)
    {T : BigHOver B S hS} (ε : T ⟶ Wd) (g' : Wd' ⟶ W)
    (β' : Functor.pullbackFiber p y g' ≅ o') (ε' : T ⟶ Wd') (r : T ⟶ W) (hr : ε ≫ g = r)
    (hr' : ε' ≫ g' = r) : IsIso (glueCmpMor g β ε g' β' ε' r hr hr') := by
  rw [glueCmpMor]
  infer_instance

namespace DescentSolution

variable (h1 : IsZariskiStackInGroupoids B S hS p)
  (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
  (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
  (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
  (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)

/-- **The comparisons of local identifications compose**, as comparisons of solutions. -/
public theorem isCmp_glueCmpMor_trans {W Wd Wd' Wd'' : BigHOver B S hS} {y : p.Fiber W}
    {F₀ : Wd ⟶ U} {F₁ : Wd' ⟶ U} {F₂ : Wd'' ⟶ U} {s₀ : DescentSolution D F₀}
    {s₁ : DescentSolution D F₁} {s₂ : DescentSolution D F₂} (g : Wd ⟶ W)
    (β : Functor.pullbackFiber p y g ≅ s₀.obj) {T : BigHOver B S hS} (ε : T ⟶ Wd) (g' : Wd' ⟶ W)
    (β' : Functor.pullbackFiber p y g' ≅ s₁.obj) (ε' : T ⟶ Wd') (g'' : Wd'' ⟶ W)
    (β'' : Functor.pullbackFiber p y g'' ≅ s₂.obj) (ε'' : T ⟶ Wd'') (r : T ⟶ W) (hr : ε ≫ g = r)
    (hr' : ε' ≫ g' = r) (hr'' : ε'' ≫ g'' = r) {q : T ⟶ U} (hq₀ : ε ≫ F₀ = q)
    (hq₁ : ε' ≫ F₁ = q)
    (hm : IsCmp s₀ ε s₁ ε' (glueCmpMor g β ε g' β' ε' r hr hr'))
    (hm' : IsCmp s₁ ε' s₂ ε'' (glueCmpMor g' β' ε' g'' β'' ε'' r hr' hr'')) :
    IsCmp s₀ ε s₂ ε'' (glueCmpMor g β ε g'' β'' ε'' r hr hr'') := by
  rw [← glueCmpMor_trans g β ε g' β' ε' g'' β'' ε'' r hr hr' hr'']
  exact IsCmp.comp hq₀ hq₁ hm hm'

include h1 h2 h3 h4 hf in
/-- **The comparison of two local identifications in the other order** is again a comparison of
solutions.  The canonical comparison in that order is a right inverse of the given one by
uniqueness, and the comparison of local identifications in the other order is another, so the two
agree because a comparison of local identifications is an isomorphism. -/
public theorem isCmp_glueCmpMor_symm {W Wd Wd' : BigHOver B S hS} {y : p.Fiber W}
    {F₀ : Wd ⟶ U} {F₁ : Wd' ⟶ U} {s₀ : DescentSolution D F₀} {s₁ : DescentSolution D F₁}
    (g : Wd ⟶ W) (β : Functor.pullbackFiber p y g ≅ s₀.obj) {T : BigHOver B S hS} (ε : T ⟶ Wd)
    (g' : Wd' ⟶ W) (β' : Functor.pullbackFiber p y g' ≅ s₁.obj) (ε' : T ⟶ Wd') (r : T ⟶ W)
    (hr : ε ≫ g = r) (hr' : ε' ≫ g' = r) {q : T ⟶ U} (hq₀ : ε ≫ F₀ = q) (hq₁ : ε' ≫ F₁ = q)
    (hm : IsCmp s₀ ε s₁ ε' (glueCmpMor g β ε g' β' ε' r hr hr')) :
    IsCmp s₁ ε' s₀ ε (glueCmpMor g' β' ε' g β ε r hr' hr) := by
  have hc := isCmp_cmpIso h1 h2 h3 h4 hf s₁ hq₁ s₀ hq₀
  have hone : glueCmpMor g β ε g' β' ε' r hr hr' ≫
      (cmpIso h1 h2 h3 h4 hf s₁ hq₁ s₀ hq₀).hom = 𝟙 _ :=
    IsCmp.eq h1 h2 h3 h4 hf hq₀ hq₀ (IsCmp.comp hq₀ hq₁ hm hc) (isCmp_id s₀ ε)
  have htwo : glueCmpMor g β ε g' β' ε' r hr hr' ≫ glueCmpMor g' β' ε' g β ε r hr' hr = 𝟙 _ := by
    rw [glueCmpMor_trans g β ε g' β' ε' g β ε r hr hr' hr, glueCmpMor_self]
  have := isIso_glueCmpMor g β ε g' β' ε' r hr hr'
  rw [← (cancel_epi (glueCmpMor g β ε g' β' ε' r hr hr')).mp (hone.trans htwo.symm)]
  exact hc

end DescentSolution

/-- A comparison of solutions of two local identifications over the corner of a pullback square is
one over every object mapping to the square, by base change. -/
private theorem isCmp_glueCmpMor_of_isPullback {W A C P : BigHOver B S hS} {y : p.Fiber W}
    {F₀ : A ⟶ U} {F₁ : C ⟶ U} {s₀ : DescentSolution D F₀} {s₁ : DescentSolution D F₁}
    {g : A ⟶ W} {k : C ⟶ W} {e : P ⟶ A} {d : P ⟶ C} (hsq : IsPullback e d g k)
    (β : Functor.pullbackFiber p y g ≅ s₀.obj) (β' : Functor.pullbackFiber p y k ≅ s₁.obj)
    (hc : DescentSolution.IsCmp s₀ e s₁ d (glueCmpMor g β e k β' d (e ≫ g) rfl hsq.w.symm))
    {T : BigHOver B S hS} (ε : T ⟶ A) (ε' : T ⟶ C) (r : T ⟶ W) (hr : ε ≫ g = r)
    (hr' : ε' ≫ k = r) : DescentSolution.IsCmp s₀ ε s₁ ε' (glueCmpMor g β ε k β' ε' r hr hr') := by
  have hw : ε ≫ g = ε' ≫ k := hr.trans hr'.symm
  have hτe := hsq.lift_fst ε ε' hw
  have hτd := hsq.lift_snd ε ε' hw
  have hτr : hsq.lift ε ε' hw ≫ (e ≫ g) = r := by rw [← Category.assoc, hτe, hr]
  rw [← glueCmpMor_baseChange g β e k β' d (e ≫ g) rfl hsq.w.symm (hsq.lift ε ε' hw) ε hτe ε' hτd
    r hτr hr hr']
  exact hc.baseChange _ ε hτe ε' hτd

/-! ### The descent datum assembled out of a family of solutions -/

/-- **The descent datum, for the pullback pseudofunctor, assembled out of a family of solutions of
`D` over a covering of `W`.**  Its objects are the objects of the solutions and its gluing
isomorphisms are the canonical comparisons
`AlgebraicGeometry.BigHOver.DescentSolution.cmpIso`; the three axioms are the three identities
those satisfy. -/
public def solutionDescentData
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    {W : BigHOver B S hS} {F : W ⟶ U} {K : Type (u + 1)} {Wc : K → BigHOver B S hS}
    {γ : ∀ c, Wc c ⟶ W} {Fc : ∀ c, Wc c ⟶ U} (hFc : ∀ c, γ c ≫ F = Fc c)
    (s : ∀ c, DescentSolution D (Fc c)) :
    (Functor.IsFibered.pullbackPseudofunctor p).DescentData γ where
  obj c := (s c).obj
  hom _T q _c _c' ε ε' hε hε' :=
    (DescentSolution.cmpIso h1 h2 h3 h4 hf (s _) (comp_eq_of_covering_fac hFc _ ε q hε) (s _)
      (comp_eq_of_covering_fac hFc _ ε' q hε')).hom
  hom_self := by
    intro T q c ε hε
    exact DescentSolution.cmpIso_hom_self h1 h2 h3 h4 hf (s c)
      (comp_eq_of_covering_fac hFc c ε q hε)
  hom_comp := by
    intro T q c c' c'' ε ε' ε'' hε hε' hε''
    exact DescentSolution.cmpIso_hom_trans h1 h2 h3 h4 hf (s c)
      (comp_eq_of_covering_fac hFc c ε q hε) (s c') (comp_eq_of_covering_fac hFc c' ε' q hε')
      (s c'') (comp_eq_of_covering_fac hFc c'' ε'' q hε'')
  pullHom_hom := by
    intro T' T g q q' hqq c c' ε ε' hε hε' gε gε' hgε hgε'
    subst hgε
    subst hgε'
    subst hqq
    rw [Functor.pullHom_eq p (s c).obj (s c').obj ε ε' g]
    exact DescentSolution.cmpIso_hom_baseChange h1 h2 h3 h4 hf (s c)
      (comp_eq_of_covering_fac hFc c ε q hε) (s c')
      (comp_eq_of_covering_fac hFc c' ε' q hε') g (g ≫ ε) rfl (g ≫ ε') rfl
      (comp_eq_of_covering_fac hFc c (g ≫ ε) (g ≫ q) (by rw [Category.assoc, hε]))
      (comp_eq_of_covering_fac hFc c' (g ≫ ε') (g ≫ q) (by rw [Category.assoc, hε']))

/-! ### Two-element families of solutions and of local identifications -/

/-- The two-element family of solutions of `D` with members `sg` and `sk`. -/
public def pairSolution {A C : BigHOver B S hS} {Fg : A ⟶ U} {Fk : C ⟶ U}
    (sg : DescentSolution D Fg) (sk : DescentSolution D Fk) :
    (i : Bool) → DescentSolution D (pairHom Fg Fk i)
  | false => sg
  | true => sk

/-- The two-element family of local identifications of `y` with the objects of `sg` and `sk`. -/
public def pairLocalIso {W A C : BigHOver B S hS} {y : p.Fiber W} {g : A ⟶ W} {k : C ⟶ W}
    {Fg : A ⟶ U} {Fk : C ⟶ U} {sg : DescentSolution D Fg} {sk : DescentSolution D Fk}
    (βg : Functor.pullbackFiber p y g ≅ sg.obj) (βk : Functor.pullbackFiber p y k ≅ sk.obj) :
    (i : Bool) → Functor.pullbackFiber p y (pairHom g k i) ≅ (pairSolution sg sk i).obj
  | false => βg
  | true => βk

/-- **A solution glued along a two-element h covering of the source.**  This is
`AlgebraicGeometry.BigHOver.nonempty_descentSolution_of_glueCmp` for the two-element family, with
the independence hypothesis spelled out as its four pairs. -/
public theorem nonempty_descentSolution_of_pair
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    {W A C : BigHOver B S hS} {F : W ⟶ U} (g : A ⟶ W) (k : C ⟶ W)
    (hcov : Sieve.ofArrows (fun j : ULift.{u + 1} Bool ↦ pairObj A C j.down)
      (fun j ↦ pairHom g k j.down) ∈ BigHOver.topology B S hS W)
    {Fg : A ⟶ U} (hFg : g ≫ F = Fg) {Fk : C ⟶ U} (hFk : k ≫ F = Fk)
    (sg : DescentSolution D Fg) (sk : DescentSolution D Fk) {y : p.Fiber W}
    (βg : Functor.pullbackFiber p y g ≅ sg.obj) (βk : Functor.pullbackFiber p y k ≅ sk.obj)
    (h00 : ∀ (T : BigHOver B S hS) (ε ε' : T ⟶ A) (r : T ⟶ W) (hr : ε ≫ g = r)
      (hr' : ε' ≫ g = r), DescentSolution.IsCmp sg ε sg ε'
        (glueCmpMor g βg ε g βg ε' r hr hr'))
    (h01 : ∀ (T : BigHOver B S hS) (ε : T ⟶ A) (ε' : T ⟶ C) (r : T ⟶ W) (hr : ε ≫ g = r)
      (hr' : ε' ≫ k = r), DescentSolution.IsCmp sg ε sk ε'
        (glueCmpMor g βg ε k βk ε' r hr hr'))
    (h10 : ∀ (T : BigHOver B S hS) (ε : T ⟶ C) (ε' : T ⟶ A) (r : T ⟶ W) (hr : ε ≫ k = r)
      (hr' : ε' ≫ g = r), DescentSolution.IsCmp sk ε sg ε'
        (glueCmpMor k βk ε g βg ε' r hr hr'))
    (h11 : ∀ (T : BigHOver B S hS) (ε ε' : T ⟶ C) (r : T ⟶ W) (hr : ε ≫ k = r)
      (hr' : ε' ≫ k = r), DescentSolution.IsCmp sk ε sk ε'
        (glueCmpMor k βk ε k βk ε' r hr hr')) :
    Nonempty (DescentSolution D F) := by
  have hFc : ∀ j : ULift.{u + 1} Bool, pairHom g k j.down ≫ F = pairHom Fg Fk j.down := by
    intro j
    obtain ⟨dd⟩ := j
    cases dd
    · exact hFg
    · exact hFk
  refine nonempty_descentSolution_of_glueCmp h1 h2 h3 h4 hcov
    (s := fun j ↦ pairSolution sg sk j.down) hFc (fun j ↦ pairLocalIso βg βk j.down) ?_
  intro c c' T ε ε' r hr hr'
  obtain ⟨dd⟩ := c
  obtain ⟨dd'⟩ := c'
  cases dd <;> cases dd'
  · exact h00 T ε ε' r hr hr'
  · exact h01 T ε ε' r hr hr'
  · exact h10 T ε ε' r hr hr'
  · exact h11 T ε ε' r hr hr'

/-! ### The object a cartesian square provides -/

/-- **The object and the identifications a cartesian square along which the comparison functor is
an equivalence provides.**  Given solutions of `D` over the centre and over the modification of the
square, essential surjectivity of
`AlgebraicGeometry.BigHOver.twoFibreProductComparison`, applied to their objects glued over the
exceptional corner by the canonical comparison, produces an object of the fibre over the base
identified with both; and the mixed pair of local identifications is then that canonical
comparison, over the corner by construction and over an arbitrary object by base change, because
the corner is the fibre product. -/
public theorem exists_glue_of_square
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    {Xb Xm Xc Xe : BigHOver B S hS} (b : Xm ⟶ Xb) (z : Xc ⟶ Xb) (d : Xe ⟶ Xm) (e : Xe ⟶ Xc)
    (hsq : IsPullback e d z b)
    (heq : (twoFibreProductComparison B S hS p b z d e hsq).IsEquivalence)
    {F : Xb ⟶ U} {Fz : Xc ⟶ U} (hFz : z ≫ F = Fz) {Fb : Xm ⟶ U} (hFb : b ≫ F = Fb)
    (sZ : DescentSolution D Fz) (sX : DescentSolution D Fb) :
    ∃ (y : p.Fiber Xb) (βz : Functor.pullbackFiber p y z ≅ sZ.obj)
      (βb : Functor.pullbackFiber p y b ≅ sX.obj),
      ∀ (T : BigHOver B S hS) (ε : T ⟶ Xc) (ε' : T ⟶ Xm) (r : T ⟶ Xb) (hr : ε ≫ z = r)
        (hr' : ε' ≫ b = r), DescentSolution.IsCmp sZ ε sX ε'
          (glueCmpMor z βz ε b βb ε' r hr hr') := by
  have hdb : d ≫ b = e ≫ z := hsq.w.symm
  have hcb : d ≫ Fb = e ≫ Fz := by
    rw [← hFb, ← Category.assoc, hdb, Category.assoc, hFz]
  obtain ⟨x, αZ0, αX0, hcond⟩ := exists_fiberObj b z d e hsq heq sZ.obj sX.obj
    (DescentSolution.cmpIso h1 h2 h3 h4 hf sZ (rfl : e ≫ Fz = e ≫ Fz) sX hcb)
  -- the two spellings of an iterated chosen pullback are crossed in term mode, through locals
  -- typed in the chosen-pullback spelling
  obtain ⟨αZ, hαZ⟩ : ∃ αZ : Functor.pullbackFiber p x z ≅ sZ.obj, αZ.hom = αZ0.hom :=
    ⟨αZ0, rfl⟩
  obtain ⟨αX, hαX⟩ : ∃ αX : Functor.pullbackFiber p x b ≅ sX.obj, αX.hom = αX0.hom :=
    ⟨αX0, rfl⟩
  have h_a : Functor.pullbackFiberHom αZ.hom e =
      (Functor.IsFibered.fiberPullback (p := p) e).map αZ0.hom :=
    (congrArg (fun m ↦ Functor.pullbackFiberHom m e) hαZ).trans
      (Functor.fiberPullback_map_eq_pullbackFiberHom (p := p) e αZ0.hom).symm
  have h_b : Functor.pullbackFiberHom αX.hom d =
      (Functor.IsFibered.fiberPullback (p := p) d).map αX0.hom :=
    (congrArg (fun m ↦ Functor.pullbackFiberHom m d) hαX).trans
      (Functor.fiberPullback_map_eq_pullbackFiberHom (p := p) d αX0.hom).symm
  have h_c : (Functor.pullbackFiberCompIso' x z e (e ≫ z) rfl).hom ≫
        (Functor.pullbackFiberCompIso' x b d (e ≫ z) hdb).inv =
      ((twoFibreProductComparison B S hS p b z d e hsq).obj x).iso.hom :=
    (cmpMor_cartComp_cartCompOfSquare b z d e hsq rfl x).symm
  have hkey : (Functor.pullbackFiberCompIso' x z e (e ≫ z) rfl).hom ≫
        (Functor.pullbackFiberCompIso' x b d (e ≫ z) hdb).inv ≫
          Functor.pullbackFiberHom αX.hom d =
      Functor.pullbackFiberHom αZ.hom e ≫
        (DescentSolution.cmpIso h1 h2 h3 h4 hf sZ (rfl : e ≫ Fz = e ≫ Fz) sX hcb).hom :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ Functor.pullbackFiberHom αX.hom d) h_c).trans
        ((congrArg
            (fun m ↦ ((twoFibreProductComparison B S hS p b z d e hsq).obj x).iso.hom ≫ m)
            h_b).trans
          (hcond.symm.trans
            (congrArg
              (fun k ↦ k ≫
                (DescentSolution.cmpIso h1 h2 h3 h4 hf sZ (rfl : e ≫ Fz = e ≫ Fz) sX hcb).hom)
              h_a).symm)))
  have hcorner : glueCmpMor z αZ e b αX d (e ≫ z) rfl hdb =
      (DescentSolution.cmpIso h1 h2 h3 h4 hf sZ (rfl : e ≫ Fz = e ≫ Fz) sX hcb).hom := by
    rw [glueCmpMor_eq z αZ e b αX d (e ≫ z) rfl hdb, localIso_inv, localIso_hom]
    simp only [Category.assoc]
    rw [hkey, ← Category.assoc, ← Functor.pullbackFiberHom_comp, αZ.inv_hom_id,
      Functor.pullbackFiberHom_id, Category.id_comp]
  refine ⟨x, αZ, αX, fun T ε ε' r hr hr' ↦
    isCmp_glueCmpMor_of_isPullback hsq αZ αX ?_ ε ε' r hr hr'⟩
  rw [hcorner]
  exact DescentSolution.isCmp_cmpIso h1 h2 h3 h4 hf sZ (rfl : e ≫ Fz = e ≫ Fz) sX hcb

/-! ### The Zariski step -/

/-- **Gluing solutions along a family with effective descent.**  Solutions of `D` over the members
of a family of `W` glue to a solution over `W`, as soon as the family generates a covering sieve of
the h topology and the functor from the fibre over `W` to the descent data relative to it is an
equivalence. -/
public theorem nonempty_descentSolution_of_isEquivalence_toDescentData
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    {W : BigHOver B S hS} {F : W ⟶ U} {K : Type (u + 1)} {Wc : K → BigHOver B S hS}
    {γ : ∀ c, Wc c ⟶ W} {Fc : ∀ c, Wc c ⟶ U} (hFc : ∀ c, γ c ≫ F = Fc c)
    (heqv : ((Functor.IsFibered.pullbackPseudofunctor p).toDescentData γ).IsEquivalence)
    (hcov : Sieve.ofArrows Wc γ ∈ BigHOver.topology B S hS W)
    (s : ∀ c, DescentSolution D (Fc c)) :
    Nonempty (DescentSolution D F) := by
  have := heqv
  obtain ⟨y, ⟨ee⟩⟩ : ∃ y : p.Fiber W, Nonempty
      (((Functor.IsFibered.pullbackPseudofunctor p).toDescentData γ).obj y ≅
        solutionDescentData h1 h2 h3 h4 hf hFc s) :=
    ⟨_, ⟨((Functor.IsFibered.pullbackPseudofunctor p).toDescentData γ).objObjPreimageIso _⟩⟩
  have hβ1 : ∀ c, Pseudofunctor.DescentData.Hom.hom ee.hom c ≫
      Pseudofunctor.DescentData.Hom.hom ee.inv c = 𝟙 _ := fun c ↦ by
    rw [← Pseudofunctor.DescentData.comp_hom, ee.hom_inv_id, Pseudofunctor.DescentData.id_hom]
  have hβ2 : ∀ c, Pseudofunctor.DescentData.Hom.hom ee.inv c ≫
      Pseudofunctor.DescentData.Hom.hom ee.hom c = 𝟙 _ := fun c ↦ by
    rw [← Pseudofunctor.DescentData.comp_hom, ee.inv_hom_id, Pseudofunctor.DescentData.id_hom]
  obtain ⟨β, hβh⟩ : ∃ β : ∀ c, Functor.pullbackFiber p y (γ c) ≅ (s c).obj,
      ∀ c, (β c).hom = Pseudofunctor.DescentData.Hom.hom ee.hom c :=
    ⟨fun c ↦ { hom := Pseudofunctor.DescentData.Hom.hom ee.hom c
               inv := Pseudofunctor.DescentData.Hom.hom ee.inv c
               hom_inv_id := hβ1 c
               inv_hom_id := hβ2 c }, fun _ ↦ rfl⟩
  refine nonempty_descentSolution_of_glueCmp h1 h2 h3 h4
    hcov hFc β ?_
  intro c c' T ε ε' r hr hr'
  have heq2 : ε ≫ γ c = ε' ≫ γ c' := by rw [hr, hr']
  -- the two spellings are crossed in term mode: the commutation condition of `ee`, restated
  -- entirely in the chosen-pullback spelling
  have hmapc : Functor.pullbackFiberHom (β c).hom ε =
      ((Functor.IsFibered.pullbackPseudofunctor p).map ε.op.toLoc).toFunctor.map
        (Pseudofunctor.DescentData.Hom.hom ee.hom c) :=
    (congrArg (fun m ↦ Functor.pullbackFiberHom m ε) (hβh c)).trans
      (Functor.pullbackPseudofunctor_map_map p ε
        (Pseudofunctor.DescentData.Hom.hom ee.hom c)).symm
  have hmapc' : Functor.pullbackFiberHom (β c').hom ε' =
      ((Functor.IsFibered.pullbackPseudofunctor p).map ε'.op.toLoc).toFunctor.map
        (Pseudofunctor.DescentData.Hom.hom ee.hom c') :=
    (congrArg (fun m ↦ Functor.pullbackFiberHom m ε') (hβh c')).trans
      (Functor.pullbackPseudofunctor_map_map p ε'
        (Pseudofunctor.DescentData.Hom.hom ee.hom c')).symm
  have htd : (((Functor.IsFibered.pullbackPseudofunctor p).toDescentData γ).obj y).hom r ε ε'
        hr hr' = (Functor.pullbackFiberComparison y ε ε' heq2).hom :=
    Functor.toDescentData_obj_hom p γ y r ε ε' hr hr' heq2
  have hcomm : (Functor.pullbackFiberComparison y ε ε' heq2).hom ≫
        Functor.pullbackFiberHom (β c').hom ε' =
      Functor.pullbackFiberHom (β c).hom ε ≫
        (DescentSolution.cmpIso h1 h2 h3 h4 hf (s c) (comp_eq_of_covering_fac hFc c ε r hr)
          (s c') (comp_eq_of_covering_fac hFc c' ε' r hr')).hom :=
    ((congrArg (fun k ↦ k ≫ (DescentSolution.cmpIso h1 h2 h3 h4 hf (s c)
            (comp_eq_of_covering_fac hFc c ε r hr) (s c')
            (comp_eq_of_covering_fac hFc c' ε' r hr')).hom) hmapc).trans
      ((ee.hom.comm r ε ε' hr hr').trans
        ((congrArg (fun k ↦ k ≫ ((Functor.IsFibered.pullbackPseudofunctor p).map
              ε'.op.toLoc).toFunctor.map
              (Pseudofunctor.DescentData.Hom.hom ee.hom c')) htd).trans
          (congrArg (fun m ↦ (Functor.pullbackFiberComparison y ε ε' heq2).hom ≫ m)
            hmapc'.symm)))).symm
  have hgl : glueCmpMor (γ c) (β c) ε (γ c') (β c') ε' r hr hr' =
      (DescentSolution.cmpIso h1 h2 h3 h4 hf (s c) (comp_eq_of_covering_fac hFc c ε r hr) (s c')
        (comp_eq_of_covering_fac hFc c' ε' r hr')).hom := by
    rw [glueCmpMor_eq (γ c) (β c) ε (γ c') (β c') ε' r hr hr', localIso_inv, localIso_hom]
    simp only [Category.assoc]
    rw [← Category.assoc (Functor.pullbackFiberCompIso' y (γ c) ε r hr).hom,
      Functor.pullbackFiberCompIso'_hom_comp_inv p y (γ c) (γ c') ε ε' r hr hr' heq2,
      hcomm, ← Category.assoc, ← Functor.pullbackFiberHom_comp, (β c).inv_hom_id,
      Functor.pullbackFiberHom_id, Category.id_comp]
  rw [hgl]
  exact DescentSolution.isCmp_cmpIso h1 h2 h3 h4 hf (s c) _ (s c') _

/-- **The Zariski step.**  Solutions of `D` over the members of a Zariski covering family of `W`
glue to a solution over `W`.

Condition (1) of Stacks 0EX9 makes the functor from the fibre over `W` to the descent data of that
family an equivalence, by Stacks 02ZF, and the family is an h covering by
`AlgebraicGeometry.BigHOver.zariskiTopology_le_topology`, so this is
`AlgebraicGeometry.BigHOver.nonempty_descentSolution_of_isEquivalence_toDescentData`. -/
public theorem nonempty_descentSolution_zariski
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    {W : BigHOver B S hS} {F : W ⟶ U} {K : Type (u + 1)} {Wc : K → BigHOver B S hS}
    {γ : ∀ c, Wc c ⟶ W} {Fc : ∀ c, Wc c ⟶ U} (hFc : ∀ c, γ c ≫ F = Fc c)
    (hzar : Sieve.ofArrows Wc γ ∈ zariskiTopology B S hS W)
    (s : ∀ c, DescentSolution D (Fc c)) :
    Nonempty (DescentSolution D F) := by
  have hzst : p.IsStack (zariskiTopology B S hS) := Functor.isStack_of_isStackInGroupoids h1
  exact nonempty_descentSolution_of_isEquivalence_toDescentData h1 h2 h3 h4 hf hFc
    (Functor.isEquivalence_toDescentData_of_isStack p hzst γ hzar)
    (zariskiTopology_le_topology B S hS _ hzar) s

/-! ### The step for a flat proper surjection of finite presentation onto an affine object -/

/-- **The step for the self-square of a flat proper surjection of finite presentation onto an
affine object.**  A solution of `D` over such a morphism `g : Xm ⟶ Xb` glues to a solution over
`Xb`, the covering being `g` itself.

Its single pair of local identifications is the mixed pair of the self-square, read twice: the two
morphisms into `Xm` agreeing over `Xb` factor through the exceptional corner `Xm ×_Xb Xm`, which is
the corner of that square. -/
public theorem nonempty_descentSolution_selfSquare
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    {Xb Xm Xe : BigHOver B S hS} (g : Xm ⟶ Xb) (pr₁ pr₂ : Xe ⟶ Xm)
    (hsq : IsPullback pr₁ pr₂ g g)
    (heq : (twoFibreProductComparison B S hS p g g pr₂ pr₁ hsq).IsEquivalence)
    (hcov : Sieve.ofArrows (fun _ : PUnit.{u + 2} ↦ Xm) (fun _ ↦ g) ∈
      BigHOver.topology B S hS Xb)
    {F : Xb ⟶ U} {Fg : Xm ⟶ U} (hFg : g ≫ F = Fg) (sG : DescentSolution D Fg) :
    Nonempty (DescentSolution D F) := by
  obtain ⟨y, βz, βb, hmix⟩ :=
    exists_glue_of_square h1 h2 h3 h4 hf g g pr₂ pr₁ hsq heq hFg hFg sG sG
  refine nonempty_descentSolution_of_glueCmp h1 h2 h3 h4 hcov
    (s := fun _ : PUnit.{u + 2} ↦ sG) (fun _ ↦ hFg) (fun _ ↦ βz) ?_
  intro _ _ T ε ε' r hr hr'
  refine DescentSolution.isCmp_glueCmpMor_trans g βz ε g βb ε' g βz ε' r hr hr'
    hr' (comp_eq_of_comp_eq hFg ε hr) (comp_eq_of_comp_eq hFg ε' hr') (hmix T ε ε' r hr hr') ?_
  exact DescentSolution.isCmp_glueCmpMor_symm h1 h2 h3 h4 hf g βz ε' g βb ε' r hr' hr'
    (comp_eq_of_comp_eq hFg ε' hr') (comp_eq_of_comp_eq hFg ε' hr') (hmix T ε' ε' r hr' hr')

/-! ### The step for an almost blowup square -/

/-- **The step for an almost blowup square.**  Solutions of `D` over the centre and over the
modification of an almost blowup square of the site glue to a solution over its base, the covering
being the two-element family `{Z ⟶ X, X' ⟶ X}` of
`AlgebraicGeometry.BigHOver.sieve_ofArrows_pair_mem_topology`.

The two mixed pairs of local identifications factor through the exceptional corner.  The pair
`(Z, Z)` is trivial because the centre is a monomorphism,
`AlgebraicGeometry.BigHOver.mono_center_of_almostBlowUpSquare`.  The pair `(X', X')` factors
through `X' ×_X X'`, over which the base change of the centre and the diagonal of the modification
form an h covering by
`AlgebraicGeometry.BigHOver.sieve_ofArrows_pair_diagonal_mem_topology`; over the diagonal the two
projections agree, and over the base change of the centre the pair is the composite of the two
mixed pairs, so
`AlgebraicGeometry.BigHOver.DescentSolution.isCmp_of_covering` concludes. -/
public theorem nonempty_descentSolution_almostBlowUpSquare
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U)
    {Xb Xm Xc Xe : BigHOver B S hS} (b : Xm ⟶ Xb) (z : Xc ⟶ Xb) (d : Xe ⟶ Xm) (e : Xe ⟶ Xc)
    (hsq : IsPullback e d z b)
    (heq : (twoFibreProductComparison B S hS p b z d e hsq).IsEquivalence)
    (Id : ((BigHOver.toScheme B S hS).obj Xb).IdealSheafData)
    (hb : IsAlmostBlowUpSquare Id ((BigHOver.toScheme B S hS).map b))
    (hZ : Nonempty (Over.mk ((BigHOver.toScheme B S hS).map z) ≅ Over.mk Id.subschemeι))
    {F : Xb ⟶ U} {Fz : Xc ⟶ U} (hFz : z ≫ F = Fz) {Fb : Xm ⟶ U} (hFb : b ≫ F = Fb)
    (sZ : DescentSolution D Fz) (sX : DescentSolution D Fb) :
    Nonempty (DescentSolution D F) := by
  have hmono : Mono z := mono_center_of_almostBlowUpSquare z Id hZ
  obtain ⟨y, βz, βb, hmix⟩ :=
    exists_glue_of_square h1 h2 h3 h4 hf b z d e hsq heq hFz hFb sZ sX
  -- the mixed pair in the other order
  have hmix' : ∀ (T : BigHOver B S hS) (ε : T ⟶ Xm) (ε' : T ⟶ Xc) (r : T ⟶ Xb)
      (hr : ε ≫ b = r) (hr' : ε' ≫ z = r), DescentSolution.IsCmp sX ε sZ ε'
        (glueCmpMor b βb ε z βz ε' r hr hr') := fun T ε ε' r hr hr' ↦
    DescentSolution.isCmp_glueCmpMor_symm h1 h2 h3 h4 hf z βz ε' b βb ε r hr' hr
      (comp_eq_of_comp_eq hFz ε' hr') (comp_eq_of_comp_eq hFb ε hr) (hmix T ε' ε r hr' hr)
  refine nonempty_descentSolution_of_pair h1 h2 h3 h4 z b
    (sieve_ofArrows_pair_mem_topology b z Id hb hZ) hFz hFb sZ sX βz βb ?_ hmix hmix' ?_
  · -- the pair `(Z, Z)`: the centre is a monomorphism
    intro T ε ε' r hr hr'
    obtain rfl : ε = ε' := (cancel_mono z).mp (by rw [hr, hr'])
    rw [glueCmpMor_self]
    exact DescentSolution.isCmp_id sZ ε
  · -- the pair `(X', X')`: the fibre square of the modification and its covering
    intro T ε ε' r hr hr'
    obtain ⟨P, f₁, f₂, hP⟩ : ∃ (P : BigHOver B S hS) (f₁ f₂ : P ⟶ Xm), IsPullback f₁ f₂ b b :=
      ⟨_, _, _, IsPullback.of_hasPullback b b⟩
    obtain ⟨dg, hd₁, hd₂⟩ : ∃ dg : Xm ⟶ P, dg ≫ f₁ = 𝟙 Xm ∧ dg ≫ f₂ = 𝟙 Xm :=
      ⟨hP.lift (𝟙 Xm) (𝟙 Xm) rfl, hP.lift_fst _ _ _, hP.lift_snd _ _ _⟩
    obtain ⟨T₀, a, rr, hT⟩ : ∃ (T₀ : BigHOver B S hS) (a : T₀ ⟶ Xc) (rr : T₀ ⟶ P),
        IsPullback a rr z (f₁ ≫ b) := ⟨_, _, _, IsPullback.of_hasPullback z (f₁ ≫ b)⟩
    have hbase : DescentSolution.IsCmp sX f₁ sX f₂
        (glueCmpMor b βb f₁ b βb f₂ (f₁ ≫ b) rfl hP.w.symm) := by
      refine DescentSolution.isCmp_of_covering h1 h2 h3 h4 hf sX (comp_eq_of_comp_eq hFb f₁ rfl) sX
        (comp_eq_of_comp_eq hFb f₂ hP.w.symm) (fun j : ULift.{u + 1} Bool ↦ pairHom rr dg j.down)
        (sieve_ofArrows_pair_diagonal_mem_topology b z f₁ f₂ hP (f₁ ≫ b) rfl a rr hT dg hd₁ hd₂
          Id hb hZ) ?_
      intro j δ₀ hδ₀ δ₁ hδ₁
      have hδ₀b : δ₀ ≫ b = pairHom rr dg j.down ≫ (f₁ ≫ b) := by
        subst hδ₀
        exact Category.assoc _ _ _
      have hδ₁b : δ₁ ≫ b = pairHom rr dg j.down ≫ (f₁ ≫ b) := by
        subst hδ₁
        rw [Category.assoc, ← hP.w]
      rw [glueCmpMor_baseChange b βb f₁ b βb f₂ (f₁ ≫ b) rfl hP.w.symm
        (pairHom rr dg j.down) δ₀ hδ₀ δ₁ hδ₁ (pairHom rr dg j.down ≫ (f₁ ≫ b)) rfl hδ₀b hδ₁b]
      obtain ⟨dd⟩ := j
      cases dd
      · -- over the base change of the centre: the composite of the two mixed pairs
        have hab : a ≫ z = rr ≫ (f₁ ≫ b) := hT.w
        refine DescentSolution.isCmp_glueCmpMor_trans b βb δ₀ z βz a b βb δ₁
          (rr ≫ (f₁ ≫ b)) hδ₀b hab hδ₁b
          (comp_eq_of_comp_eq hFb δ₀ hδ₀b) (comp_eq_of_comp_eq hFz a hab)
          (hmix' _ δ₀ a _ hδ₀b hab) (hmix _ a δ₁ _ hab hδ₁b)
      · -- over the diagonal: the two projections agree
        obtain rfl : δ₀ = 𝟙 Xm := hδ₀.symm.trans hd₁
        obtain rfl : δ₁ = 𝟙 Xm := hδ₁.symm.trans hd₂
        rw [glueCmpMor_self]
        exact DescentSolution.isCmp_id sX (𝟙 Xm)
    have hw : ε ≫ b = ε' ≫ b := by rw [hr, hr']
    have hσ₁ : hP.lift ε ε' hw ≫ f₁ = ε := hP.lift_fst ε ε' hw
    have hσ₂ : hP.lift ε ε' hw ≫ f₂ = ε' := hP.lift_snd ε ε' hw
    have hσr : hP.lift ε ε' hw ≫ (f₁ ≫ b) = r := by rw [← Category.assoc, hσ₁, hr]
    rw [← glueCmpMor_baseChange b βb f₁ b βb f₂ (f₁ ≫ b) rfl hP.w.symm (hP.lift ε ε' hw) ε hσ₁
      ε' hσ₂ r hσr hr hr']
    exact DescentSolution.IsCmp.baseChange hbase (hP.lift ε ε' hw) ε hσ₁ ε' hσ₂

/-! ### A solution over the base -/

/-- **A solution of `D` over `𝟙 U` exists.**

This is `AlgebraicGeometry.BigHOver.of_localOnGenerators` for the property that a solution of `D`
over an object of the slice at `U` exists: it is stable under precomposition by
`AlgebraicGeometry.BigHOver.DescentSolution.baseChange`, its Zariski step is
`AlgebraicGeometry.BigHOver.nonempty_descentSolution_zariski`, its step for a flat proper
surjection `g` of finite presentation onto an affine object is
`AlgebraicGeometry.BigHOver.nonempty_descentSolution_of_isEquivalence_toDescentData` for the
one-element family `{g}`, by condition (2), and its two remaining steps are two instantiations of
`AlgebraicGeometry.BigHOver.nonempty_descentSolution_almostBlowUpSquare`.  It holds over each
member of the covering family because the object of the datum there is a solution,
`AlgebraicGeometry.BigHOver.descentSolutionOfObj`. -/
public theorem nonempty_descentSolution_id
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hf : Sieve.ofArrows V f ∈ BigHOver.topology B S hS U) :
    Nonempty (DescentSolution D (𝟙 U)) := by
  classical
  refine of_localOnGenerators B S hS U (fun Y ↦ Nonempty (DescentSolution D Y.hom))
    (fun k hY ↦ ⟨hY.some.baseChange k.left _ (Over.w k)⟩) ?_ ?_ ?_ ?_ f hf
    (fun i ↦ ⟨descentSolutionOfObj D i⟩)
  · -- the Zariski step
    intro Y E hE hloc
    have hcov : Sieve.ofArrows (fun i ↦ (E.X i).left) (fun i ↦ (E.f i).left) ∈
        zariskiTopology B S hS Y.left :=
      Precoverage.generate_mem_toGrothendieck
        ⟨⟨E.I₀, fun i ↦ (E.X i).left, fun i ↦ (E.f i).left⟩, rfl, hE⟩
    exact nonempty_descentSolution_zariski h1 h2 h3 h4 hf (fun i ↦ Over.w (E.f i)) hcov
      fun i ↦ (hloc i).some
  · -- a flat proper surjection of finite presentation onto an affine object: effective descent
    -- along the one-element family `{g}`, which is condition (2)
    intro Y Y' g hAff hflat hproper hsurj hfp hY'
    -- the hypotheses are stated for `sliceToScheme`, which is `toScheme` precomposed with
    -- `Over.forget U`; instance search does not see through that, so they are restated
    have hsurj' : Surjective ((BigHOver.toScheme B S hS).map g.left) := hsurj
    have hproper' : IsProper ((BigHOver.toScheme B S hS).map g.left) := hproper
    have hE : IsHCovering
        ((PreZeroHypercover.singleton.{u + 1} g.left).map (BigHOver.toScheme B S hS)).X
        ((PreZeroHypercover.singleton.{u + 1} g.left).map (BigHOver.toScheme B S hS)).f :=
      (surjective_proper_isHCovering ((BigHOver.toScheme B S hS).map g.left) hfp).reindex
        (Equiv.ofUnique PUnit.{u + 2} Unit)
    exact nonempty_descentSolution_of_isEquivalence_toDescentData h1 h2 h3 h4 hf
      (Wc := fun _ : PUnit.{u + 2} ↦ Y'.left) (fun _ ↦ Over.w g)
      (h2 Y.left Y'.left g.left hAff hflat hproper hsurj hfp)
      (sieve₀_mem_topology_of_isHCovering B S hS
        (PreZeroHypercover.singleton.{u + 1} g.left) hE) fun _ ↦ hY'.some
  · -- the square of Example 0EVG
    intro Xb X' Z Xe b z q e Id hAff hbb hZ hsq hmod hZΨ hX'Ψ
    have hsq' : IsPullback e.left q.left z.left b.left :=
      IsPullback.of_map_of_faithful (BigHOver.toScheme B S hS) hsq
    exact nonempty_descentSolution_almostBlowUpSquare h1 h2 h3 h4 hf b.left z.left q.left e.left
      hsq' (h3 Xb.left X'.left Z.left Xe.left b.left z.left q.left e.left Id hAff hbb hZ hsq' hsq
        hmod) Id hbb hZ (Over.w z) (Over.w b) hZΨ.some hX'Ψ.some
  · -- the square of Example 0EVH
    intro Xb X' Z Xe b z q e Id hAff hbb hZ hsq hmod hZΨ hX'Ψ
    have hsq' : IsPullback e.left q.left z.left b.left :=
      IsPullback.of_map_of_faithful (BigHOver.toScheme B S hS) hsq
    exact nonempty_descentSolution_almostBlowUpSquare h1 h2 h3 h4 hf b.left z.left q.left e.left
      hsq' (h4 Xb.left X'.left Z.left Xe.left b.left z.left q.left e.left Id hAff hbb hZ hsq' hsq
        hmod) Id hbb hZ (Over.w z) (Over.w b) hZΨ.some hX'Ψ.some

end BigHOver

end AlgebraicGeometry

end
