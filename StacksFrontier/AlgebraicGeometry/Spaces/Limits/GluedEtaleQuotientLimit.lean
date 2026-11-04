module

public import Mathlib.CategoryTheory.Filtered.Final
public import StacksFrontier.AlgebraicGeometry.Spaces.ElementaryDistinguishedSquarePushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GluedEtaleQuotientSystem
public import StacksFrontier.CategoryTheory.Limits.CartesianTransformationLimit

/-!
# The limit of an inverse system of glued étale quotients

For an inverse system of glued étale data whose ambient objects `Vⱼ` have a limit `Vinf` in
presheaves, the limit `X' = lim Xⱼ` of the quotients receives a map `Vinf ⟶ X'`, and every square

```
Vinf ---> Vⱼ
|       |
v       v
X' ---> Xⱼ
```

is cartesian. Consequently `Vinf ⟶ X'` is surjective and étale. Moreover, the kernel pair of
`Vinf ⟶ X'` is the glued relation of the limit data.

## Main results

* `isPullback_limitChart`: the square formed by `Vinf ⟶ Vⱼ`, `Vinf ⟶ X'`, `Vⱼ ⟶ Xⱼ` and
  `X' ⟶ Xⱼ` is cartesian.
* `isPullback_limitChart_kernel`: the kernel pair of the limit chart `Vinf ⟶ X'` is the relation
  glued from the limit data.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.GluedEtaleQuotient.System

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})} {J : Type u} [Category.{u} J]
  [IsCofiltered J] (D : System B hZ J)
  (cV : Cone (D.ambient ⋙ yoneda)) (hcV : IsLimit cV)

/-- The quotient maps, as a natural transformation into the system of quotients. -/
def chartNat : D.ambient ⋙ yoneda ⟶ D.quotients where
  app := D.chartMap
  naturality _ _ g := (D.chartMap_transition g).symm

/-- The chart `Vinf ⟶ X' = lim Xⱼ` of the limit. -/
abbrev limitChart : cV.pt ⟶ limit D.quotients :=
  limit.lift D.quotients ((Cones.postcompose D.chartNat).obj cV)

omit [IsCofiltered J] in
/-- The limit chart followed by the projection to `Xⱼ` is the projection to `Vⱼ` followed by
the quotient map `Vⱼ ⟶ Xⱼ`. -/
@[reassoc (attr := simp)]
theorem limitChart_π (j : J) :
    D.limitChart cV ≫ limit.π D.quotients j = cV.π.app j ≫ D.chartMap j :=
  limit.lift_π _ _

include hcV in
/-- **The square `Vinf = Vⱼ ×_{Xⱼ} X'` is cartesian.** -/
theorem isPullback_limitChart (j : J) :
    IsPullback (cV.π.app j) (D.limitChart cV) (D.chartMap j) (limit.π D.quotients j) :=
  isPullback_of_isLimit_of_cartesian D.chartNat (fun g => (D.isPullback_chartMap g).flip) hcV
    (limit.isLimit D.quotients) (D.limitChart cV) (fun j => (limitChart_π D cV j).symm) j

/-! ### The kernel pair of the limit chart -/

section KernelPair

variable {Uinf : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
  {Winf Vinf : BigFppfOver B (⊤_ Scheme.{u}) hZ}
  (winf : yoneda.obj Winf ⟶ Uinf)
  (hwinf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf winf)
  (ιinf : Winf ⟶ Vinf)
  [AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ιinf)]
  (πU : (Functor.const J).obj Uinf ⟶ D.base) (πW : (Functor.const J).obj Winf ⟶ D.chart)
  (πV : (Functor.const J).obj Vinf ⟶ D.ambient)
  (hwU : ∀ j, winf ≫ πU.app j = yoneda.map (πW.app j) ≫ D.toBase.app j)
  (hιV : ∀ j, ιinf ≫ πV.app j = πW.app j ≫ D.incl.app j)
  (hWU : ∀ j, IsPullback (yoneda.map (πW.app j)) winf (D.toBase.app j) (πU.app j))
  (hWV : ∀ j, IsPullback ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (πW.app j))
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map ιinf)
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (D.incl.app j))
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (πV.app j)))
  (hVinf : IsLimit (yoneda.mapCone (Cone.mk Vinf πV)))

/-- The relation map from the limit data to a stage. -/
abbrev relProj (j : J) :
    relationObj winf hwinf ιinf ⟶ relationObj (D.toBase.app j) (D.etale j) (D.incl.app j) :=
  relationMap (D.toBase.app j) (D.etale j) (D.incl.app j) winf hwinf ιinf (πU.app j) (πW.app j)
    (πV.app j) (hwU j) (hιV j)

omit [IsCofiltered J] in
include hwU hιV in
/-- The relation maps from the limit data to the stages commute with the transition maps of the
system of relations. -/
theorem relProj_naturality {a b : J} (g : a ⟶ b) :
    D.relProj winf hwinf ιinf πU πW πV hwU hιV a ≫ D.relations.map g =
      D.relProj winf hwinf ιinf πU πW πV hwU hιV b := by
  have nV : πV.app b = πV.app a ≫ D.ambient.map g := ((Cone.mk Vinf πV).w g).symm
  have nW : πW.app b = πW.app a ≫ D.chart.map g := ((Cone.mk Winf πW).w g).symm
  apply relation_hom_ext
  · show inlV winf hwinf ιinf ≫ D.relProj winf hwinf ιinf πU πW πV hwU hιV a ≫
      D.relTransition g = inlV winf hwinf ιinf ≫ D.relProj winf hwinf ιinf πU πW πV hwU hιV b
    rw [inlV_relationMap_assoc, inlV_relationMap, inlV_relationMap, nV, Category.assoc]
  · show inrQ winf hwinf ιinf ≫ D.relProj winf hwinf ιinf πU πW πV hwU hιV a ≫
      D.relTransition g = inrQ winf hwinf ιinf ≫ D.relProj winf hwinf ιinf πU πW πV hwU hιV b
    rw [inrQ_relationMap_assoc, inrQ_relationMap, inrQ_relationMap, ← Category.assoc]
    congr 1
    apply (D.etale b).rep.hom_ext'
    · simp [nW]
    · simp [nW]

/-- The cone of relations over the limit data. -/
abbrev relCone : Cone D.relations :=
  Cone.mk (relationObj winf hwinf ιinf) (NatTrans.mk (D.relProj winf hwinf ιinf πU πW πV hwU hιV)
    (fun _ _ g => (Category.id_comp _).trans
      (D.relProj_naturality winf hwinf ιinf πU πW πV hwU hιV g).symm))

/-- A cartesian square of schemes between objects of the site is cartesian in the site. -/
theorem isPullback_of_toScheme {P X Y Z : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (h : IsPullback ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map fst)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map snd)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map f)
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map g)) :
    IsPullback fst snd f g :=
  IsPullback.of_map (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ) w h

omit [IsCofiltered J] in
include hwU hιV in
/-- The relation map to stage `j` is compatible with the source maps of the relations. -/
theorem relProj_src (j : J) :
    D.relProj winf hwinf ιinf πU πW πV hwU hιV j ≫ src (D.toBase.app j) (D.etale j) (D.incl.app j) =
      src winf hwinf ιinf ≫ πV.app j :=
  relationMap_src _ _ _ _ _ _ _ _ _ _ _

omit [IsCofiltered J] in
include hwU hιV in
/-- The relation map to stage `j` is compatible with the target maps of the relations. -/
theorem relProj_tgt (j : J) :
    D.relProj winf hwinf ιinf πU πW πV hwU hιV j ≫ tgt (D.toBase.app j) (D.etale j) (D.incl.app j) =
      tgt winf hwinf ιinf ≫ πV.app j :=
  relationMap_tgt _ _ _ _ _ _ _ _ _ _ _

include hwU hιV hWU hWV hVinf in
/-- **The kernel pair of the limit chart `V∞ ⟶ lim Xⱼ` is the glued relation of the limit
data.** -/
theorem isPullback_limitChart_kernel :
    IsPullback (yoneda.map (tgt winf hwinf ιinf)) (yoneda.map (src winf hwinf ιinf))
      (D.limitChart (yoneda.mapCone (Cone.mk Vinf πV)))
      (D.limitChart (yoneda.mapCone (Cone.mk Vinf πV))) := by
  set cV := yoneda.mapCone (Cone.mk Vinf πV) with hcVdef
  set f' := D.limitChart cV with hf'def
  have hα : ∀ {a b : J} (g : a ⟶ b), IsPullback ((D.relations ⋙ yoneda).map g)
      ((Functor.whiskerRight D.srcNat yoneda).app a) ((Functor.whiskerRight D.srcNat yoneda).app b)
      ((D.ambient ⋙ yoneda).map g) := fun g =>
    (isPullback_of_toScheme (D.srcNat.naturality g) (D.isPullback_relations g)).map yoneda
  have hcart : ∀ j, IsPullback
      ((yoneda.mapCone (D.relCone winf hwinf ιinf πU πW πV hwU hιV)).π.app j)
      (yoneda.map (src winf hwinf ιinf)) ((Functor.whiskerRight D.srcNat yoneda).app j)
      (cV.π.app j) := fun j =>
    (isPullback_of_toScheme (D.relProj_src winf hwinf ιinf πU πW πV hwU hιV j)
      (isPullback_relationMap _ _ _ _ _ _ _ _ _ (hwU j) (hιV j) (hWU j) (hWV j))).map yoneda
  have hR := isLimitOfCartesian (Functor.whiskerRight D.srcNat yoneda) hα hVinf
    (yoneda.mapCone (D.relCone winf hwinf ιinf πU πW πV hwU hιV))
    (yoneda.map (src winf hwinf ιinf)) hcart
  have hker : ∀ j, IsPullback (yoneda.map (tgt (D.toBase.app j) (D.etale j) (D.incl.app j)))
      (yoneda.map (src (D.toBase.app j) (D.etale j) (D.incl.app j)))
      (D.chartMap j) (D.chartMap j) := fun j => isPullback_qmap _ _ _
  have ρt : ∀ j, yoneda.map (D.relProj winf hwinf ιinf πU πW πV hwU hιV j) ≫
      yoneda.map (tgt (D.toBase.app j) (D.etale j) (D.incl.app j)) =
        yoneda.map (tgt winf hwinf ιinf) ≫ cV.π.app j := fun j => by
    rw [← yoneda.map_comp, relProj_tgt, yoneda.map_comp]; rfl
  have ρs : ∀ j, yoneda.map (D.relProj winf hwinf ιinf πU πW πV hwU hιV j) ≫
      yoneda.map (src (D.toBase.app j) (D.etale j) (D.incl.app j)) =
        yoneda.map (src winf hwinf ιinf) ≫ cV.π.app j := fun j => by
    rw [← yoneda.map_comp, relProj_src, yoneda.map_comp]; rfl
  have hw : yoneda.map (tgt winf hwinf ιinf) ≫ f' = yoneda.map (src winf hwinf ιinf) ≫ f' := by
    refine limit.hom_ext fun j => ?_
    rw [Category.assoc, Category.assoc, limitChart_π, ← Category.assoc, ← ρt,
      ← Category.assoc, ← ρs, Category.assoc, Category.assoc, (hker j).w]
  have hcond : ∀ (s : PullbackCone f' f') (j : J), (s.fst ≫ cV.π.app j) ≫ D.chartMap j =
      (s.snd ≫ cV.π.app j) ≫ D.chartMap j := fun s j => by
    rw [Category.assoc, Category.assoc, ← limitChart_π, ← Category.assoc,
      ← Category.assoc, s.condition]
  let ℓ (s : PullbackCone f' f') (j : J) :
      s.pt ⟶ yoneda.obj (relationObj (D.toBase.app j) (D.etale j) (D.incl.app j)) :=
    (hker j).lift (s.fst ≫ cV.π.app j) (s.snd ≫ cV.π.app j) (hcond s j)
  have ℓ_tgt : ∀ (s : PullbackCone f' f') (j : J),
      ℓ s j ≫ yoneda.map (tgt (D.toBase.app j) (D.etale j) (D.incl.app j)) =
        s.fst ≫ cV.π.app j := fun s j => (hker j).lift_fst _ _ _
  have ℓ_src : ∀ (s : PullbackCone f' f') (j : J),
      ℓ s j ≫ yoneda.map (src (D.toBase.app j) (D.etale j) (D.incl.app j)) =
        s.snd ≫ cV.π.app j := fun s j => (hker j).lift_snd _ _ _
  have hcVw : ∀ {a b : J} (g : a ⟶ b), cV.π.app a ≫ yoneda.map (D.ambient.map g) = cV.π.app b :=
    fun g => cV.w g
  have ℓ_nat : ∀ (s : PullbackCone f' f') {a b : J} (g : a ⟶ b),
      ℓ s a ≫ yoneda.map (D.relTransition g) = ℓ s b := by
    intro s a b g
    have hRs : D.relTransition g ≫ src (D.toBase.app b) (D.etale b) (D.incl.app b) =
        src (D.toBase.app a) (D.etale a) (D.incl.app a) ≫ D.ambient.map g :=
      relationMap_src _ _ _ _ _ _ _ _ _ _ _
    have hRt : D.relTransition g ≫ tgt (D.toBase.app b) (D.etale b) (D.incl.app b) =
        tgt (D.toBase.app a) (D.etale a) (D.incl.app a) ≫ D.ambient.map g :=
      relationMap_tgt _ _ _ _ _ _ _ _ _ _ _
    apply relation_yoneda_jointlyMono (D.toBase.app b) (D.etale b) (D.incl.app b)
    · rw [Category.assoc, ← yoneda.map_comp, hRs, yoneda.map_comp, ← Category.assoc, ℓ_src,
        Category.assoc, hcVw, ℓ_src]
    · rw [Category.assoc, ← yoneda.map_comp, hRt, yoneda.map_comp, ← Category.assoc, ℓ_tgt,
        Category.assoc, hcVw, ℓ_tgt]
  let cone (s : PullbackCone f' f') : Cone (D.relations ⋙ yoneda) :=
    Cone.mk s.pt (NatTrans.mk (ℓ s) (fun a b g => (Category.id_comp _).trans (ℓ_nat s g).symm))
  have hfac : ∀ (s : PullbackCone f' f') (j : J),
      hR.lift (cone s) ≫ yoneda.map (D.relProj winf hwinf ιinf πU πW πV hwU hιV j) = ℓ s j :=
    fun s j => hR.fac (cone s) j
  have fac₁ : ∀ s : PullbackCone f' f', hR.lift (cone s) ≫ yoneda.map (tgt winf hwinf ιinf) =
      s.fst := fun s => by
    refine hVinf.hom_ext fun j => ?_
    show _ ≫ cV.π.app j = s.fst ≫ cV.π.app j
    rw [Category.assoc, ← ρt j, ← Category.assoc, hfac, ℓ_tgt]
  have fac₂ : ∀ s : PullbackCone f' f', hR.lift (cone s) ≫ yoneda.map (src winf hwinf ιinf) =
      s.snd := fun s => by
    refine hVinf.hom_ext fun j => ?_
    show _ ≫ cV.π.app j = s.snd ≫ cV.π.app j
    rw [Category.assoc, ← ρs j, ← Category.assoc, hfac, ℓ_src]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => hR.lift (cone s)) fac₁ fac₂
    (fun s m hm₁ hm₂ => ?_)⟩⟩
  exact relation_yoneda_jointlyMono winf hwinf ιinf m _ (by rw [hm₂, fac₂]) (by rw [hm₁, fac₁])

end KernelPair

end AlgebraicGeometry.Space.GluedEtaleQuotient.System

end
