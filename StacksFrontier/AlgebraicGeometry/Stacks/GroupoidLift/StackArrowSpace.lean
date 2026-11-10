module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackArrowIsom
public import StacksFrontier.CategoryTheory.Sites.Localization.LowerShriekCoproducts
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.ChartPostcomp

/-!
# The arrows of the groupoid of a chart as points of an isomorphism space

With the notation of `AlgebraicGeometry.Stack.GroupoidLift.StackChart.morToArr`, let
`Isom(x₀, x₁)` be the isomorphism presheaf of `x₀ = ξ v₀` and `x₁ = ξ vₗ` on the slice of the big
fppf site over `Spec (P ⊗ P)`, and let `R` be its coproduct presheaf on the big fppf site of `S`
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.arrSpace`): a section of `R` over `W` is a
morphism `φ : W ⟶ Spec (P ⊗ P)` together with an isomorphism of the chosen pullbacks of `x₀`
and `x₁` along `φ`. Through `Spec (P ⊗ P) ⟶ T'` it lies over `T'`.

The points of `R` over `T'` with values in a small `A'`-algebra `C` are the arrows of the
groupoid of the chart over `C`, naturally in `C`
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart.relToArr`).

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.arrSpace`, `arrSpaceToBase`.
* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.relToArr`, `relToArrNat`: the natural
  bijection.
* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.arrChart`: the chart of the arrows given by a
  point of the space of arrows.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.relToArrNat_bijective`.
* `AlgebraicGeometry.Stack.GroupoidLift.StackChart.arrChart_isFormallyEtale`: the chart of a
  formally étale point is formally étale; `arrChart_src`, `arrChart_tgt` compute its source and
  target.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} (a : schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  {P : SmallAlg (ringOf B S hS T') B.cutoff} (ι : specOver P ⟶ U₀)

namespace StackChart

/-- The projection of a category fibred in groupoids is fibered. -/
local instance : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered

/-- The isomorphism presheaf of `x₀` and `x₁` on the slice over `Spec (P ⊗ P)`. -/
noncomputable abbrev pairIsom : (Over (specOver (pairAlg P)))ᵒᵖ ⥤ Type u :=
  𝒳.val.p.isomPresheaf (pairObj₀ a ι) (pairObj₁ a ι)

/-- **The space of arrows**: the coproduct presheaf of the isomorphism presheaf. -/
noncomputable abbrev arrSpace : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  OverShriek.presheaf (pairIsom a ι)

/-- The space of arrows lies over `T'`. -/
noncomputable abbrev arrSpaceToBase : arrSpace a ι ⟶ yoneda.obj T' :=
  OverShriek.presheafToYoneda (pairIsom a ι) ≫ yoneda.map (specOverToBase (pairAlg P))

/-- The comparison of the point `Spec h` with a point `φ` it is equal to. -/
noncomputable abbrev pairOverTo {C : SmallAlg (ringOf B S hS T') B.cutoff}
    {φ : specOver C ⟶ specOver (pairAlg P)} (h : pairAlg P ⟶ C) (p : specOverMap h = φ) :
    pairOver P h.hom.hom ⟶ Over.mk φ :=
  Over.homMk (𝟙 _) ((Category.id_comp _).trans p.symm)

/-- The arrow of a section of the isomorphism presheaf over a point equal to `Spec h`. -/
noncomputable def isomToArr {C : SmallAlg (ringOf B S hS T') B.cutoff}
    {φ : specOver C ⟶ specOver (pairAlg P)} (h : pairAlg P ⟶ C) (p : specOverMap h = φ)
    (s : (pairIsom a ι).obj (op (Over.mk φ))) : Arr a ι C :=
  morToArr a ι h.hom.hom ((pairIsom a ι).map (pairOverTo h p).op s).1

/-- The arrow `isomToArr h p s` does not depend on the choice of `h` with `Spec h = φ`. -/
theorem isomToArr_congr {C : SmallAlg (ringOf B S hS T') B.cutoff}
    {φ : specOver C ⟶ specOver (pairAlg P)} (h₁ h₂ : pairAlg P ⟶ C) (p₁ : specOverMap h₁ = φ)
    (p₂ : specOverMap h₂ = φ) (s : (pairIsom a ι).obj (op (Over.mk φ))) :
    isomToArr a ι h₁ p₁ s = isomToArr a ι h₂ p₂ s := by
  obtain rfl := specOverMap_injective (p₁.trans p₂.symm)
  rfl

/-- **The arrow of a point of the space of arrows over `T'`.** -/
noncomputable def relToArr {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (r : (relPoints T' (arrSpaceToBase a ι)).obj C) : Arr a ι C :=
  isomToArr a ι (exists_specOverMap r.1.1 r.2).choose (exists_specOverMap r.1.1 r.2).choose_spec
    r.1.2

/-- The arrow of a point of the space of arrows over `T'` lying over `Spec h` is
`isomToArr h p` of its section. -/
theorem relToArr_eq {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (r : (relPoints T' (arrSpaceToBase a ι)).obj C) (h : pairAlg P ⟶ C)
    (p : specOverMap h = r.1.1) : relToArr a ι r = isomToArr a ι h p r.1.2 :=
  isomToArr_congr a ι _ _ _ _ _

/-- The point of the space of arrows given by a point `Spec h` of `Spec (P ⊗ P)` and a section of
the isomorphism presheaf over it. -/
noncomputable def arrPt {C : SmallAlg (ringOf B S hS T') B.cutoff} (h : pairAlg P ⟶ C)
    (s : (pairIsom a ι).obj (op (pairOver P h.hom.hom))) :
    (relPoints T' (arrSpaceToBase a ι)).obj C :=
  ⟨⟨specOverMap h, s⟩, specOverMap_comp_toBase h⟩

/-- The arrow of the point `arrPt h s` is `morToArr` of the isomorphism `s`. -/
theorem relToArr_arrPt {C : SmallAlg (ringOf B S hS T') B.cutoff} (h : pairAlg P ⟶ C)
    (s : (pairIsom a ι).obj (op (pairOver P h.hom.hom))) :
    relToArr a ι (arrPt a ι h s) = morToArr a ι h.hom.hom s.1 := by
  refine (relToArr_eq a ι _ h rfl).trans ?_
  have e : pairOverTo (P := P) h rfl = 𝟙 _ := Over.OverMorphism.ext rfl
  change morToArr a ι h.hom.hom ((pairIsom a ι).map (pairOverTo h rfl).op s).1 = _
  rw [e, op_id]
  exact congrArg (fun t => morToArr a ι h.hom.hom (Subtype.val t))
    ((pairIsom a ι).map_id_apply _ s)

/-- Every point of the space of arrows over `T'` is of the form `arrPt h s`. -/
theorem exists_arrPt {C : SmallAlg (ringOf B S hS T') B.cutoff}
    (r : (relPoints T' (arrSpaceToBase a ι)).obj C) :
    ∃ (h : pairAlg P ⟶ C) (s : (pairIsom a ι).obj (op (pairOver P h.hom.hom))),
      arrPt a ι h s = r := by
  obtain ⟨⟨φ, s⟩, hφ⟩ := r
  obtain ⟨h, rfl⟩ := exists_specOverMap φ hφ
  exact ⟨h, s, rfl⟩

/-- A morphism of a fibre of a category fibred in groupoids is an isomorphism. -/
theorem isIso_fiber_hom {W : BigFppfOver B S hS} {x y : 𝒳.val.p.Fiber W} (m : x ⟶ y) :
    IsIso m := by
  have := m.2
  have := 𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 W) m.1
  have : IsIso m.1 := Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒳.val.p (𝟙 W) m.1
  exact ⟨⟨⟨CategoryTheory.inv m.1, inferInstance⟩, Functor.Fiber.hom_ext (IsIso.hom_inv_id m.1),
    Functor.Fiber.hom_ext (IsIso.inv_hom_id m.1)⟩⟩

/-- **The arrow of a point is injective.** -/
theorem relToArr_injective {C : SmallAlg (ringOf B S hS T') B.cutoff} :
    Function.Injective (relToArr a ι (C := C)) := by
  intro r r' e
  obtain ⟨h, s, rfl⟩ := exists_arrPt a ι r
  obtain ⟨h', s', rfl⟩ := exists_arrPt a ι r'
  rw [relToArr_arrPt, relToArr_arrPt] at e
  obtain rfl : h = h' := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    exact pair_ext P (congrArg Arr.src e) (congrArg Arr.tgt e)
  rw [Subtype.ext (morToArr_injective a ι _ e)]

/-- **The arrow of a point is surjective.** -/
theorem relToArr_surjective {C : SmallAlg (ringOf B S hS T') B.cutoff} :
    Function.Surjective (relToArr a ι (C := C)) := by
  intro g
  obtain ⟨h, m, rfl⟩ := exists_morToArr_eq a ι g
  exact ⟨_, relToArr_arrPt a ι (SmallAlg.homMk h) ⟨m, isIso_fiber_hom m⟩⟩

/-- **The arrow of a point is natural.** -/
theorem relToArr_map {C D : SmallAlg (ringOf B S hS T') B.cutoff} (f : C ⟶ D)
    (r : (relPoints T' (arrSpaceToBase a ι)).obj C) :
    relToArr a ι ((relPoints T' (arrSpaceToBase a ι)).map f r) =
      Arr.map a ι f (relToArr a ι r) := by
  obtain ⟨h, s, rfl⟩ := exists_arrPt a ι r
  rw [relToArr_arrPt, map_morToArr]
  refine (relToArr_eq a ι _ (h ≫ f) (specOverMap_comp h f)).trans ?_
  have e : pairOverTo (h ≫ f) (specOverMap_comp h f) ≫
      (Over.homMk (specOverMap f) rfl : Over.mk (specOverMap f ≫ specOverMap h) ⟶
        Over.mk (specOverMap h)) = pairOverMap f h.hom.hom :=
    Over.OverMorphism.ext (Category.id_comp _)
  change morToArr a ι (h ≫ f).hom.hom ((pairIsom a ι).map (pairOverTo (h ≫ f)
    (specOverMap_comp h f)).op ((pairIsom a ι).map (Over.homMk (specOverMap f) rfl :
      Over.mk (specOverMap f ≫ specOverMap h) ⟶ Over.mk (specOverMap h)).op s)).1 = _
  rw [OverShriek.map_op_comp, e]
  rfl

/-- **The points of the space of arrows over `T'` are the arrows**, as a natural transformation. -/
noncomputable def relToArrNat : relPoints T' (arrSpaceToBase a ι) ⟶ stackArr a ι where
  app C := TypeCat.ofHom (relToArr a ι (C := C))
  naturality _ _ f := by
    ext r
    exact relToArr_map a ι f r

/-- Each component of `relToArrNat` is a bijection. -/
theorem relToArrNat_bijective (C : SmallAlg (ringOf B S hS T') B.cutoff) :
    Function.Bijective ((relToArrNat a ι).app C) :=
  ⟨relToArr_injective a ι, relToArr_surjective a ι⟩

/-- **The chart of the arrows given by a point of the space of arrows.** -/
noncomputable def arrChart (Q : SmallAlg (ringOf B S hS T') B.cutoff)
    (q : (relPoints T' (arrSpaceToBase a ι)).obj Q) : Chart (stackArr a ι) Q.obj :=
  chartPostcomp (relChart (arrSpaceToBase a ι) Q q) (relToArrNat a ι)

/-- The chart of the arrows of a formally étale point is formally étale. -/
theorem arrChart_isFormallyEtale (Q : SmallAlg (ringOf B S hS T') B.cutoff)
    (q : (relPoints T' (arrSpaceToBase a ι)).obj Q)
    (hq : Space.FormallyEtale (yonedaEquiv.symm q.1)) : (arrChart a ι Q q).IsFormallyEtale :=
  chartPostcomp_isFormallyEtale (relChart_isFormallyEtale _ Q q hq) _ (relToArrNat_bijective a ι)

/-- The value of the chart `arrChart Q q` at `v : Q → C` is the image of `relToArr q` by `v`. -/
theorem arrChart_app (Q : SmallAlg (ringOf B S hS T') B.cutoff)
    (q : (relPoints T' (arrSpaceToBase a ι)).obj Q) (C : SmallAlg (ringOf B S hS T') B.cutoff)
    (v : Q.obj →ₐ[ringOf B S hS T'] C.obj) :
    (arrChart a ι Q q).app C v = Arr.map a ι (SmallAlg.homMk v) (relToArr a ι q) :=
  relToArr_map a ι (SmallAlg.homMk v) q

/-- The source of the chart of the arrows. -/
theorem arrChart_src (Q : SmallAlg (ringOf B S hS T') B.cutoff)
    (q : (relPoints T' (arrSpaceToBase a ι)).obj Q) (C : SmallAlg (ringOf B S hS T') B.cutoff)
    (v : Q.obj →ₐ[ringOf B S hS T'] C.obj) :
    ((arrChart a ι Q q).app C v).src = v.comp (relToArr a ι q).src := by
  rw [arrChart_app]
  rfl

/-- The target of the chart of the arrows. -/
theorem arrChart_tgt (Q : SmallAlg (ringOf B S hS T') B.cutoff)
    (q : (relPoints T' (arrSpaceToBase a ι)).obj Q) (C : SmallAlg (ringOf B S hS T') B.cutoff)
    (v : Q.obj →ₐ[ringOf B S hS T'] C.obj) :
    ((arrChart a ι Q q).app C v).tgt = v.comp (relToArr a ι q).tgt := by
  rw [arrChart_app]
  rfl

end StackChart

end AlgebraicGeometry.Stack.GroupoidLift

end
