module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismComp
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality

/-!
# A flat morphism of algebraic stacks restricts to the flat-fppf sites

Let `f : 𝒳 ⟶ 𝒴` be a flat 1-morphism of algebraic stacks over a scheme `S` in a big fppf site
`B`. An object of `𝒳` is *flat* when the 1-morphism it names under the 2-Yoneda lemma, out of
the category represented by the scheme it lies over, is flat; the flat objects form the
flat-fppf site of **Stacks 0787**. Because flatness of 1-morphisms is stable under composition
(**Stacks 06PX**), `f` carries flat objects of `𝒳` to flat objects of `𝒴`, hence restricts to a
functor of the two flat-fppf sites, and that restriction is continuous and cocontinuous.

## Main definitions

* `AlgebraicGeometry.Stack.objectMorphismComp_twoIso`: the 2-isomorphism identifying the
  composite of the 2-Yoneda 1-morphism of an object `x` of `𝒳` with `f` and the 2-Yoneda
  1-morphism of the object `f x` of `𝒴`.
* `AlgebraicGeometry.Stack.FlatFppf.siteFunctor`: the restriction of a flat 1-morphism to the
  flat-fppf sites, together with the equality of composites that specifies it.

## Main results

* `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_twoIso` and
  `AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_of_eqToHom_comp`: the existential
  smooth-diagram criterion of **Stacks 06FM** is invariant under a 2-isomorphism of its
  1-morphism and under an identification of its source.
* `AlgebraicGeometry.Stack.FlatFppf.flatObject_map`: a flat 1-morphism carries flat objects to
  flat objects.
* `AlgebraicGeometry.Stack.FlatFppf.siteFunctor_isContinuous` and
  `AlgebraicGeometry.Stack.FlatFppf.siteFunctor_isCocontinuous`: the restriction is continuous
  and cocontinuous — **Stacks 07AT** (2), first assertion.
* `CategoryTheory.Functor.isContinuous_of_comp_fullyFaithful` and
  `CategoryTheory.Functor.isCocontinuous_of_comp_fullyFaithful`: continuity and cocontinuity
  descend from a composite along a fully faithful functor which is, respectively, cocontinuous
  and continuous.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
* [Stacks Project, Tag 06PX](https://stacks.math.columbia.edu/tag/06PX)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

namespace AlgebraicGeometry.Stack

universe u w v u₁ u₂ u₃ v₁ v₂ v₃

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The existential smooth-diagram criterion is invariant under a 2-isomorphism of its
1-morphism. -/
theorem hasPropertyOnSomeSmoothDiagram_of_twoIso
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {f g : 𝒳 ⟶ 𝒴} (e : f ≅ g)
    (hf : HasPropertyOnSomeSmoothDiagram B S hS P f) :
    HasPropertyOnSomeSmoothDiagram B S hS P g := by
  obtain ⟨U, V, hU, hV, a, b, h, ⟨η⟩, ha, hsurj, hb, hP⟩ := hf
  exact ⟨U, V, hU, hV, a, b, h,
    ⟨η ≪≫ Bicategory.whiskerLeftIso a e⟩, ha, hsurj, hb, hP⟩

/-- The existential smooth-diagram criterion holds for `g` as soon as it holds for the
precomposition of `g` with the `eqToHom` of an equality of sources. -/
theorem hasPropertyOnSomeSmoothDiagram_of_eqToHom_comp
    (P : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    {𝒳 𝒳' 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (e : 𝒳 = 𝒳') (g : 𝒳' ⟶ 𝒴)
    (hg : HasPropertyOnSomeSmoothDiagram B S hS P
      (Bicategory.InducedBicategory.mkHom
        (eqToHom (congrArg (fun Z : CatFiberedInGroupoids
          (BigFppfOver B S hS) => Z.val) e)) ≫ g)) :
    HasPropertyOnSomeSmoothDiagram B S hS P g := by
  subst 𝒳'
  exact hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS P (λ_ g) hg

/-- The value at the terminal object of the slice over `U` of the `eqToHom` identification of
the represented categories fibred in groupoids attached to an equality `U = V`. -/
theorem eqToHom_schemeFibredCategory_obj_unit
    (U V : BigFppfOver B S hS) (e : U = V) :
    ∃ hleft : ((eqToHom (congrArg (fun Z : CatFiberedInGroupoids
        (BigFppfOver B S hS) => Z.val)
        (congrArg (schemeFibredCategory B S hS) e))).toFunctor.obj
          (Over.mk (𝟙 U))).left = U,
      ((eqToHom (congrArg (fun Z : CatFiberedInGroupoids
        (BigFppfOver B S hS) => Z.val)
        (congrArg (schemeFibredCategory B S hS) e))).toFunctor.obj
          (Over.mk (𝟙 U))).hom = eqToHom hleft ≫ eqToHom e := by
  cases e
  exact ⟨rfl, rfl⟩

variable {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- For an object `x` of `𝒳` and a 1-morphism `f : 𝒳 ⟶ 𝒴`, the composite `x : U → 𝒳 → 𝒴` is
canonically 2-isomorphic to the 2-Yoneda 1-morphism of the object `f x` of `𝒴`, read over `U`
through the equality `p_𝒴 (f x) = p_𝒳 x` that `f` being strictly over the site supplies. -/
def objectMorphismComp_twoIso (f : 𝒳 ⟶ 𝒴) (x : 𝒳.val.val.obj) :
    ((Bicategory.InducedBicategory.mkHom
        (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := x) rfl)) :
        schemeStack B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳) ≫ f).hom ≅
      Bicategory.InducedBicategory.mkHom
        (eqToHom (congrArg (fun Z : CatFiberedInGroupoids
          (BigFppfOver B S hS) => Z.val)
          (congrArg (schemeFibredCategory B S hS)
            (Functor.congr_obj f.hom.hom.w x).symm)) ≫
          (objectMorphism B S hS 𝒴.val
            (Functor.Fiber.mk (a := f.hom.hom.toFunctor.obj x) rfl)).hom) := by
  let pX := 𝒳.val.val.p
  let pY := 𝒴.val.val.p
  let U := pX.obj x
  let xX : pX.Fiber U := ⟨x, rfl⟩
  have hfx : pY.obj (f.hom.hom.toFunctor.obj x) = U :=
    Functor.congr_obj f.hom.hom.w x
  let xY : pY.Fiber U := ⟨f.hom.hom.toFunctor.obj x, hfx⟩
  let LX := Functor.TwoYoneda.liftBased pX 𝒳.val.isFiberedInGroupoids U xX
  let Eₓ := Functor.twoYonedaEvaluation pX U
  let Eᵧ := Functor.twoYonedaEvaluation pY U
  let V := pY.obj (f.hom.hom.toFunctor.obj x)
  let xYV : pY.Fiber V := ⟨f.hom.hom.toFunctor.obj x, rfl⟩
  let j := eqToHom (congrArg (fun Z : CatFiberedInGroupoids
      (BigFppfOver B S hS) => Z.val)
      (congrArg (schemeFibredCategory B S hS) hfx.symm))
  let m := (objectMorphism B S hS 𝒴.val
    (Functor.Fiber.mk (a := f.hom.hom.toFunctor.obj x) rfl)).hom
  let K := j ≫ m
  let q := Functor.Fiber.fiberInclusion (p := pX) (S := U) ⋙ f.hom.hom.toFunctor
  have hq : q ⋙ pY = (Functor.const (pX.Fiber U)).obj U := by
    dsimp [q]
    rw [Functor.assoc, f.hom.hom.w]
    exact Functor.Fiber.fiberInclusion_comp_eq_const
  let F := Functor.Fiber.inducedFunctor hq
  have ex : Eₓ.obj LX ≅ xX :=
    fiberIsoOfHomLift B S hS pX 𝒳.val.isFiberedInGroupoids U
      (a := Eₓ.obj LX) (b := xX)
      (Functor.TwoYoneda.chosenLift pX 𝒳.val.isFiberedInGroupoids U
        xX (Over.mk (𝟙 U))).φ
      (Functor.TwoYoneda.chosenLift pX 𝒳.val.isFiberedInGroupoids U
        xX (Over.mk (𝟙 U))).isStronglyCartesian.toIsHomLift
  have eK : Eᵧ.obj K ≅ xY := by
    haveI := 𝒴.val.isFiberedInGroupoids.fiber_isGroupoid U
    let a := j.toFunctor.obj (Over.mk (𝟙 U))
    let targetLift := Functor.TwoYoneda.chosenLift pY
      𝒴.val.isFiberedInGroupoids V xYV a
    letI : pY.IsStronglyCartesian a.hom targetLift.φ :=
      targetLift.isStronglyCartesian
    letI : pY.IsHomLift a.hom targetLift.φ :=
      targetLift.isStronglyCartesian.toIsHomLift
    let hbase := eqToHom_schemeFibredCategory_obj_unit B S hS U V hfx.symm
    have hleft : a.left = U := by
      simpa [a, j] using Classical.choose hbase
    have ha_hom : a.hom = eqToHom hleft ≫ eqToHom hfx.symm := by
      simpa [a, j, hleft] using Classical.choose_spec hbase
    have ha : IsIso a.hom := by
      rw [ha_hom]
      infer_instance
    letI : IsIso targetLift.φ :=
      Functor.IsStronglyCartesian.isIso_of_base_isIso pY a.hom targetLift.φ
    have hdom : pY.obj targetLift.y = U :=
      (IsHomLift.domain_eq pY a.hom targetLift.φ).trans hleft
    have hlift : pY.IsHomLift (𝟙 U) targetLift.φ := by
      apply IsHomLift.of_fac' pY (𝟙 U) targetLift.φ hdom hfx
      let d := IsHomLift.domain_eq pY a.hom targetLift.φ
      let c := IsHomLift.codomain_eq pY a.hom targetLift.φ
      calc
        pY.map targetLift.φ = eqToHom d ≫ a.hom ≫ eqToHom c.symm :=
          IsHomLift.fac' pY a.hom targetLift.φ
        _ = eqToHom d ≫ (eqToHom hleft ≫ eqToHom hfx.symm) ≫ eqToHom c.symm := by
          rw [ha_hom]
        _ = eqToHom hdom ≫ (𝟙 U) ≫ eqToHom hfx.symm := by
          simp [hfx, eqToHom_trans]
    exact fiberIsoOfHomLift B S hS pY 𝒴.val.isFiberedInGroupoids U
      (a := Eᵧ.obj K) (b := xY) targetLift.φ hlift
  let G := LX ≫ f.hom.hom
  have hev : Eᵧ.obj G = F.obj (Eₓ.obj LX) := Subtype.ext rfl
  have ee : Eᵧ.obj G ≅ Eᵧ.obj K := by
    rw [hev]
    exact F.mapIso ex ≪≫ eK.symm
  letI : Eᵧ.IsEquivalence := Functor.twoYonedaEvaluation_isEquivalence pY
    𝒴.val.isFiberedInGroupoids U
  have hff : Eᵧ.FullyFaithful := Eᵧ.asEquivalence.fullyFaithfulFunctor
  let e := hff.preimageIso ee
  exact {
    hom := Bicategory.InducedBicategory.Hom₂.mk e.hom
    inv := Bicategory.InducedBicategory.Hom₂.mk e.inv
    hom_inv_id := by ext; exact e.hom_inv_id
    inv_hom_id := by ext; exact e.inv_hom_id }

namespace FlatFppf

/-- A flat 1-morphism carries flat objects to flat objects. -/
theorem flatObject_map (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsFlat B S hS f)
    (x : FlatFppf B S hS 𝒳) :
    flatObject B S hS 𝒴.val
      (f.hom.hom.toFunctor.obj ((inclusion B S hS 𝒳).obj x)) := by
  set y := (inclusion B S hS 𝒳).obj x
  let gx : schemeStack B S hS (𝒳.val.val.p.obj y) ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl))
  have hcomp : AlgebraicStacks.IsFlat B S hS (gx ≫ f) :=
    AlgebraicStacks.isFlat_comp B S hS gx f x.property hf
  have hbase : 𝒴.val.val.p.obj (f.hom.hom.toFunctor.obj y) = 𝒳.val.val.p.obj y :=
    Functor.congr_obj f.hom.hom.w y
  have hj := hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS
    (fun _ _ g => Space.IsFlat B S hS g)
    (objectMorphismComp_twoIso B S hS f y) hcomp
  exact hasPropertyOnSomeSmoothDiagram_of_eqToHom_comp B S hS
    (fun _ _ g => Space.IsFlat B S hS g)
    (congrArg (schemeFibredCategory B S hS) hbase.symm)
    (objectMorphism B S hS 𝒴.val
      (Functor.Fiber.mk (a := f.hom.hom.toFunctor.obj y) rfl)) hj

/-- If `G` is fully faithful and cocontinuous and the composite `F ⋙ G` is continuous, then `F` is
continuous. -/
theorem _root_.CategoryTheory.Functor.isContinuous_of_comp_fullyFaithful
    {C D E : Type v} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    (F : C ⥤ D) (G : D ⥤ E)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)
    [G.Full] [G.Faithful] [G.IsCocontinuous K L]
    [(F ⋙ G).IsContinuous J L] : F.IsContinuous J K := by
  constructor
  intro P
  let Q : Sheaf L (Type max u v) :=
    ⟨G.op.ran.obj P.obj, ran_isSheaf_of_isCocontinuous G L P⟩
  exact Presieve.isSheaf_iso J (Functor.isoWhiskerLeft F.op (asIso (G.op.ranCounit.app P.obj)))
    ((F ⋙ G).op_comp_isSheaf_of_types J L Q)

/-- If `G` is fully faithful and continuous and the composite `F ⋙ G` is cocontinuous, then `F`
is cocontinuous. -/
theorem _root_.CategoryTheory.Functor.isCocontinuous_of_comp_fullyFaithful
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D) (G : D ⥤ E)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : GrothendieckTopology E)
    [G.Full] [G.Faithful] [G.IsContinuous K L]
    [(F ⋙ G).IsCocontinuous J L] : F.IsCocontinuous J K := by
  constructor
  intro U R hR
  simpa only [Sieve.functorPullback_comp, Sieve.functorPullback_functorPushforward_eq] using
    (F ⋙ G).cover_lift J L ((CoverPreserving.of_isContinuous G K L).cover_preserve hR)

/-- The restriction of a flat 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` to a functor
between the flat-fppf sites, specified by the property that its composite with the inclusion of
the flat objects of `𝒴` is the inclusion of those of `𝒳` followed by the underlying functor of
`f`. -/
@[stacks 07AT "the functor of flat-fppf sites along a flat 1-morphism"]
def siteFunctor (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsFlat B S hS f) :
    {F : FlatFppf B S hS 𝒳 ⥤ FlatFppf B S hS 𝒴 //
      F ⋙ inclusion B S hS 𝒴 =
        inclusion B S hS 𝒳 ⋙ f.hom.hom.toFunctor} := by
  refine ⟨ObjectProperty.lift _
      (inclusion B S hS 𝒳 ⋙ f.hom.hom.toFunctor)
      (fun x => flatObject_map B S hS f hf x), ?_⟩
  exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => by simp [ObjectProperty.lift])

/-- The underlying functor of a 1-morphism `f` of algebraic stacks is continuous and cocontinuous
for the fppf topologies the two stacks inherit from the big fppf site of `S`. -/
theorem isContinuous_and_isCocontinuous_homFunctor (f : 𝒳 ⟶ 𝒴) :
    f.hom.hom.toFunctor.IsContinuous
        (associatedTopology B S hS 𝒳.val.val.p B.topology)
        (associatedTopology B S hS 𝒴.val.val.p B.topology) ∧
      f.hom.hom.toFunctor.IsCocontinuous
        (associatedTopology B S hS 𝒳.val.val.p B.topology)
        (associatedTopology B S hS 𝒴.val.val.p B.topology) := by
  have _ : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  have _ : 𝒴.val.val.p.IsFibered := 𝒴.val.isFiberedInGroupoids.isFibered
  have hF := 𝒴.val.isFiberedInGroupoids.isFibredOneMorphism f.hom.hom.w
  exact hF.isContinuous_and_isCocontinuous_inheritedTopology
    (B.topology.over (B.obj hS))

/-- The restriction of a flat 1-morphism to the flat-fppf sites is continuous. -/
@[stacks 07AT "that functor is continuous"]
theorem siteFunctor_isContinuous (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsFlat B S hS f) :
    (siteFunctor B S hS f hf).1.IsContinuous
      (topology B S hS 𝒳) (topology B S hS 𝒴) := by
  have hf' : f.hom.hom.toFunctor.IsContinuous
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology) :=
    (isContinuous_and_isCocontinuous_homFunctor B S hS f).1
  have hiX : (inclusion B S hS 𝒳).IsContinuous (topology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology) :=
    isContinuous_inclusion_topology B S hS 𝒳
  have hiY : (inclusion B S hS 𝒴).IsCocontinuous (topology B S hS 𝒴)
      (associatedTopology B S hS 𝒴.val.val.p B.topology) :=
    isCocontinuous_inclusion_topology B S hS 𝒴
  have : ((siteFunctor B S hS f hf).1 ⋙ inclusion B S hS 𝒴).IsContinuous
      (topology B S hS 𝒳) (associatedTopology B S hS 𝒴.val.val.p B.topology) := by
    rw [(siteFunctor B S hS f hf).2]
    exact Functor.isContinuous_comp _ _ _ (associatedTopology B S hS 𝒳.val.val.p B.topology) _
  exact Functor.isContinuous_of_comp_fullyFaithful _ (inclusion B S hS 𝒴) _ _
    (associatedTopology B S hS 𝒴.val.val.p B.topology)

/-- The restriction of a flat 1-morphism to the flat-fppf sites is cocontinuous. -/
@[stacks 07AT "that functor is cocontinuous"]
theorem siteFunctor_isCocontinuous (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsFlat B S hS f) :
    (siteFunctor B S hS f hf).1.IsCocontinuous
      (topology B S hS 𝒳) (topology B S hS 𝒴) := by
  have hf' : f.hom.hom.toFunctor.IsCocontinuous
      (associatedTopology B S hS 𝒳.val.val.p B.topology)
      (associatedTopology B S hS 𝒴.val.val.p B.topology) :=
    (isContinuous_and_isCocontinuous_homFunctor B S hS f).2
  have hiX : (inclusion B S hS 𝒳).IsCocontinuous (topology B S hS 𝒳)
      (associatedTopology B S hS 𝒳.val.val.p B.topology) :=
    isCocontinuous_inclusion_topology B S hS 𝒳
  have hiY : (inclusion B S hS 𝒴).IsContinuous (topology B S hS 𝒴)
      (associatedTopology B S hS 𝒴.val.val.p B.topology) :=
    isContinuous_inclusion_topology B S hS 𝒴
  have : ((siteFunctor B S hS f hf).1 ⋙ inclusion B S hS 𝒴).IsCocontinuous
      (topology B S hS 𝒳) (associatedTopology B S hS 𝒴.val.val.p B.topology) := by
    rw [(siteFunctor B S hS f hf).2]
    exact isCocontinuous_comp _ _ _ (associatedTopology B S hS 𝒳.val.val.p B.topology)
  exact Functor.isCocontinuous_of_comp_fullyFaithful _ (inclusion B S hS 𝒴) _ _
    (associatedTopology B S hS 𝒴.val.val.p B.topology)

end FlatFppf

end AlgebraicGeometry.Stack

end
