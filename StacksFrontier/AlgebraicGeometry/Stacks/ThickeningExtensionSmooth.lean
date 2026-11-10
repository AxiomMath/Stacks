module

public import StacksFrontier.AlgebraicGeometry.Smooth.NilpotentLifting
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.CategoryTheory.Sites.Stack.SquareCocone
public import StacksFrontier.CategoryTheory.TwoFibreProduct.TwoYonedaPairs

/-!
# Extending lifts along a smooth morphism of algebraic stacks across thickenings

Let `f : 𝒰 ⟶ 𝒳` be a smooth surjective 1-morphism of algebraic stacks over `S`, let
`i : T ⟶ T'` be a morphism of the big fppf site of `S`, let `x'` be an object of `𝒳` over `T'`
and let `u` be an object of `𝒰` over `T` with a morphism `α : f(u) ⟶ x'` over `i`. Then there
is a smooth surjective morphism `m : Tc ⟶ T` with the following extension property: for every
finite-order thickening `j : V ⟶ V'` of affine objects and every commutative square
`r ≫ m ≫ i = j ≫ r'` with `r : V ⟶ Tc` and `r' : V' ⟶ T'`, the restriction of `u` to `V` extends
to an object `u'` of `𝒰` over `V'` together with a morphism `f(u') ⟶ x'` over `r'` which is
compatible with `α` on `V`.

This is the infinitesimal lifting property of the base change `(Sch/T') ×_𝒳 𝒰 ⟶ (Sch/T')`,
which is a smooth morphism, read through a smooth chart of that 2-fibre product: the chart is a
scheme `V₀` with a smooth morphism `q : V₀ ⟶ T'`, the section `(i, u, α)` of the 2-fibre product
over `T` lifts to the chart after the smooth surjective base change `m`, and a lift into the
chart extends across `j` because `q` is a smooth morphism of schemes
(`Stacks.Smooth.exists_lift_of_isFiniteOrderThickening`).

## Main results

* `AlgebraicGeometry.Stack.exists_smooth_extension_of_isFiniteOrderThickening`: the extension
  property above.

## Implementation notes

The 2-fibre product is the canonical one of `CategoryTheory.TwoFibreProductOver`, whose objects
are quadruples, so the extended object of `𝒰` is the second component of the image of the
extended chart point, and the morphism to `x'` is read off from its comparison isomorphism. The
compatibility with `α` comes down to the defining property of the functor of chosen lifts of
the 2-Yoneda lemma: composing its value on an arrow with the chosen lift at the target gives
the chosen lift at the source.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor.TwoYoneda

-- The fibre of a functor is a plain `def`, so goals mentioning an object of a fibre are not
-- type-correct at `implicit` transparency unless it is unfolded.
attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] (p : 𝒮 ⥤ C) (hp : p.IsFiberedInGroupoids) (U : C)
  (x : p.Fiber U) (q : 𝒴 ⥤ C) (G : 𝒴 ⥤ 𝒮)

/-- The morphism to `x` attached to an object `(V, a, y, φ)` of the 2-fibre product of the
functor of chosen lifts of `x` and a functor `G`: the comparison isomorphism `φ⁻¹ : G y ≅ L a`
followed by the chosen lift of `x` along `a`. -/
noncomputable def twoFibreProductToObj
    (w : TwoFibreProductOver (Over.forget U) q p (liftFunctor p hp U x) G) :
    G.obj w.y ⟶ x.1 :=
  w.iso.inv ≫ TwoFibreProductOver.TwoYonedaPair.chosenHom hp x w.x

/-- The morphisms to `x` attached to the objects of the 2-fibre product are natural. -/
theorem map_b_comp_twoFibreProductToObj
    {w₁ w₂ : TwoFibreProductOver (Over.forget U) q p (liftFunctor p hp U x) G}
    (h : w₁ ⟶ w₂) :
    G.map h.b ≫ twoFibreProductToObj p hp U x q G w₂ = twoFibreProductToObj p hp U x q G w₁ := by
  have hw : (liftFunctor p hp U x).map h.a ≫ w₂.iso.hom = w₁.iso.hom ≫ G.map h.b := h.w
  have hL := TwoFibreProductOver.TwoYonedaPair.map_comp_chosenHom hp x h.a
  have h2 : w₁.iso.inv ≫ (liftFunctor p hp U x).map h.a = G.map h.b ≫ w₂.iso.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hw, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [twoFibreProductToObj, twoFibreProductToObj, ← hL, ← reassoc_of% h2]

end CategoryTheory.Functor.TwoYoneda

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Extension of lifts across finite-order thickenings, along a smooth surjective
1-morphism of algebraic stacks.** -/
theorem exists_smooth_extension_of_isFiniteOrderThickening
    {𝒰 𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)
    (hsurj : IsSurjective B S hS f) (hsm : AlgebraicStacks.IsSmooth B S hS f)
    {T T' : BigFppfOver B S hS} (i : T ⟶ T') (x' : 𝒳.val.val.obj) (u : 𝒰.val.val.obj)
    (α : (CatFiberedInGroupoids.homFunctor f.hom).obj u ⟶ x')
    (hα : 𝒳.val.val.p.IsHomLift i α) :
    ∃ (Tc : BigFppfOver B S hS) (m : Tc ⟶ T),
      Smooth ((BigFppfOver.toScheme B S hS).map m) ∧
      Surjective ((BigFppfOver.toScheme B S hS).map m) ∧
      ∀ {V V' : BigFppfOver B S hS} (j : V ⟶ V') (r : V ⟶ Tc) (r' : V' ⟶ T'),
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj V') →
        Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map j) →
        r ≫ m ≫ i = j ≫ r' →
        ∃ (z u' : 𝒰.val.val.obj) (μ : z ⟶ u') (ν : z ⟶ u)
          (ψ : (CatFiberedInGroupoids.homFunctor f.hom).obj u' ⟶ x'),
          𝒰.val.val.p.IsHomLift j μ ∧ 𝒰.val.val.p.IsHomLift (r ≫ m) ν ∧
          𝒳.val.val.p.IsHomLift r' ψ ∧
          (CatFiberedInGroupoids.homFunctor f.hom).map μ ≫ ψ =
            (CatFiberedInGroupoids.homFunctor f.hom).map ν ≫ α := by
  classical
  let F := CatFiberedInGroupoids.homFunctor f.hom
  have hX := 𝒳.val.isFiberedInGroupoids
  have hx'T : 𝒳.val.val.p.obj x' = T' := IsHomLift.codomain_eq _ i α
  have huT : 𝒰.val.val.p.obj u = T := by
    have h1 : 𝒳.val.val.p.obj (F.obj u) = T := IsHomLift.domain_eq _ i α
    rw [← h1]
    exact (congrArg (fun G => G.obj u) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)).symm
  let y : 𝒳.val.val.p.Fiber T' := Functor.Fiber.mk hx'T
  let L := Functor.TwoYoneda.liftBased 𝒳.val.val.p hX T' y
  let Y : schemeFibredCategory B S hS T' ⟶ 𝒳.val := Bicategory.InducedBicategory.mkHom L
  let b : schemeStack.{u, w} B S hS T' ⟶ 𝒳 := Bicategory.InducedBicategory.mkHom Y
  let P : Bicategory.TwoCommSq b f := twoFibreProductSquareAlgebraicStacks B S hS b f
  have hP : Bicategory.IsTwoFibreProduct P :=
    isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS b f
  have hPsurj : IsSurjective B S hS P.fst :=
    isSurjective_of_isTwoFibreProduct B S hS P.swap
      (Bicategory.isTwoFibreProduct_swap hP) hsurj
  have hPsm : AlgebraicStacks.IsSmooth B S hS P.fst :=
    AlgebraicStacks.isSmooth_baseChange B S hS f b P hP hsm
  obtain ⟨V₀, c, hcsm, hcsurj⟩ := exists_smooth_surjective_schemeStack.{u, w} B S hS P.pt
  have hwsurj : IsSurjective B S hS (c ≫ P.fst) :=
    isSurjective_comp B S hS c P.fst hcsurj hPsurj
  have hwsm : AlgebraicStacks.IsSmooth B S hS (c ≫ P.fst) :=
    AlgebraicStacks.isSmooth_comp B S hS c P.fst hcsm hPsm
  obtain ⟨q, hqsm, -, ⟨e⟩⟩ :=
    exists_schemeMap_of_isSurjective_isSmooth B S hS (c ≫ P.fst) hwsurj hwsm
  -- the section of the 2-fibre product over `T` given by `(i, u, α)`
  let ai : Over T' := Over.mk i
  let li := Functor.TwoYoneda.chosenLift 𝒳.val.val.p hX T' y ai
  let α' : F.obj u ⟶ x' := α
  have hα' : 𝒳.val.val.p.IsHomLift i α' := hα
  have hli : 𝒳.val.val.p.IsHomLift i li.φ := li.isStronglyCartesian.toIsHomLift
  have hii : i = 𝟙 T ≫ i := (Category.id_comp i).symm
  let γ : F.obj u ⟶ li.y :=
    @Functor.IsFiberedInGroupoids.fill _ _ _ _ _ hX _ _ _ i (𝟙 T) i hii _ _ _ li.φ hli α' hα'
  have hγ : 𝒳.val.val.p.IsHomLift (𝟙 T) γ :=
    @Functor.IsFiberedInGroupoids.fill_isHomLift _ _ _ _ _ hX _ _ _ i (𝟙 T) i hii _ _ _ li.φ hli
      α' hα'
  have : IsIso γ := hX.isIso_of_isHomLift_isIso (𝟙 T) γ
  let s : TwoFibreProductOver (BasedCategory.ofFunctor (Over.forget T')).p 𝒰.val.val.p
      𝒳.val.val.p L.toFunctor F :=
    { base := T, x := ai, y := u, hx := rfl, hy := huT, iso := (asIso γ).symm,
      vertical := by
        change 𝒳.val.val.p.IsHomLift (𝟙 T) (inv γ)
        infer_instance }
  let sF : P.pt.val.val.p.Fiber T := Functor.Fiber.mk (a := s) rfl
  obtain ⟨T₀, m₀, hm₀sm, hm₀surj, xc, αc, hαc⟩ :=
    exists_scheme_lift_of_isSurjective_isSmooth B S hS c hcsurj hcsm T sF
  let Tc : BigFppfOver B S hS := Over.mk (m₀ ≫ T.hom)
  let m : Tc ⟶ T := Over.homMk m₀ rfl
  let cF := CatFiberedInGroupoids.homFunctor c.hom
  let fstF := P.fst.hom.hom
  let sndF := P.snd.hom.hom
  -- the chart point and its morphism to `V₀`
  have hcobj : ∀ z, P.pt.val.val.p.obj (cF.obj z) = z.left := fun z =>
    congrArg (fun G => G.obj z) (CatFiberedInGroupoids.homFunctor_comp_p c.hom)
  have hxc : xc.left = Tc := by
    rw [← hcobj xc]
    exact IsHomLift.domain_eq _ m αc
  have hαc' : P.pt.val.val.p.IsHomLift m αc := hαc
  let v : Tc ⟶ V₀ := eqToHom hxc.symm ≫ xc.hom
  -- `v ≫ q = m ≫ i`
  have hvq : v ≫ q = m ≫ i := by
    have h₁ : (Over.forget T').IsHomLift m (fstF.map αc) :=
      BasedFunctor.preserves_isHomLift (F := fstF) (f := m) (φ := αc)
    have h₂ : (Over.forget T').IsHomLift (𝟙 xc.left) (e.inv.hom.app xc) :=
      e.inv.hom.isHomLift' xc
    have h₃ : (Over.forget T').IsHomLift m (e.inv.hom.app xc ≫ fstF.map αc) :=
      @IsHomLift.comp_lift_id_left' _ _ _ _ (Over.forget T') _ _ _ xc.left (e.inv.hom.app xc) h₂
        _ _ m (fstF.map αc) h₁
    have hw : (Over.forget T').map (e.inv.hom.app xc ≫ fstF.map αc) ≫ ai.hom =
        xc.hom ≫ q := Over.w (e.inv.hom.app xc ≫ fstF.map αc)
    have hfac := IsHomLift.fac' (Over.forget T') m (e.inv.hom.app xc ≫ fstF.map αc)
    rw [hfac] at hw
    simp only [v, Category.assoc, ← hw]
    have key : ∀ {A : BigFppfOver B S hS} (h₁ : Tc = A) (h₂ : A = Tc) (h₃ : T = T),
        eqToHom h₁ ≫ (eqToHom h₂ ≫ m ≫ eqToHom h₃) ≫ i = m ≫ i := by
      intro A h₁ h₂ h₃
      subst h₁
      simp
    exact key _ _ _
  refine ⟨Tc, m, hm₀sm, hm₀surj, ?_⟩
  intro V V' j r r' hV hV' hj hsq
  let toS := BigFppfOver.toScheme B S hS
  -- extend the chart point across `j`, by smoothness of `q`
  have hsq' : toS.map (r ≫ v) ≫ toS.map q = toS.map j ≫ toS.map r' := by
    rw [← toS.map_comp, ← toS.map_comp, Category.assoc, hvq, hsq]
  have := hqsm
  have := hV
  have := hV'
  obtain ⟨g', hg'q, hjg'⟩ := Stacks.Smooth.exists_lift_of_isFiniteOrderThickening (toS.map q)
    (toS.map j) hj (toS.map (r ≫ v)) (toS.map r') hsq'
  let v'l : V'.left ⟶ V₀.left := ObjectProperty.homMk g'
  have hv'l : v'l ≫ q.left = r'.left := ObjectProperty.hom_ext _ hg'q
  let v' : V' ⟶ V₀ := Over.homMk v'l (by rw [← Over.w q, ← Category.assoc, hv'l, Over.w r'])
  have hv'q : v' ≫ q = r' := Over.OverMorphism.ext hv'l
  have hjv' : j ≫ v' = r ≫ v :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hjg')
  -- the morphism to `x'` attached to an object of the 2-fibre product, and its naturality
  let ψ : ∀ w : P.pt.val.val.obj, F.obj (sndF.obj w) ⟶ x' := fun w =>
    Functor.TwoYoneda.twoFibreProductToObj 𝒳.val.val.p hX T' y 𝒰.val.val.p F w
  have hψ : ∀ {w₁ w₂ : P.pt.val.val.obj} (h : w₁ ⟶ w₂), F.map (sndF.map h) ≫ ψ w₂ = ψ w₁ :=
    fun h => Functor.TwoYoneda.map_b_comp_twoFibreProductToObj 𝒳.val.val.p hX T' y
      𝒰.val.val.p F h
  have hψs : ψ s = α :=
    @Functor.IsFiberedInGroupoids.fill_fac _ _ _ _ _ hX _ _ _ i (𝟙 T) i hii _ _ _ li.φ hli α' hα'
  -- the extended chart point and the two restriction maps
  let μc : (Over.mk (j ≫ v') : Over V₀) ⟶ Over.mk v' := Over.homMk j rfl
  let νc : (Over.mk (j ≫ v') : Over V₀) ⟶ xc := Over.homMk (r ≫ eqToHom hxc.symm) (by
    rw [Category.assoc]
    exact hjv'.symm)
  have hμc : (schemeStack.{u, w} B S hS V₀).val.val.p.IsHomLift j μc := by
    apply IsHomLift.of_fac' _ _ _ rfl rfl
    simp only [eqToHom_refl, Category.id_comp]
    rfl
  have hνc : (schemeStack.{u, w} B S hS V₀).val.val.p.IsHomLift r νc := by
    apply IsHomLift.of_fac' _ _ _ rfl hxc
    simp only [eqToHom_refl, Category.id_comp]
    change r ≫ eqToHom hxc.symm = _
    rfl
  let A := cF.map μc
  let N := cF.map νc ≫ αc
  have hA : P.pt.val.val.p.IsHomLift j A :=
    BasedFunctor.preserves_isHomLift (F := c.hom.hom) (f := j) (φ := μc)
  have hN₁ : P.pt.val.val.p.IsHomLift r (cF.map νc) :=
    BasedFunctor.preserves_isHomLift (F := c.hom.hom) (f := r) (φ := νc)
  have hN : P.pt.val.val.p.IsHomLift (r ≫ m) N := IsHomLift.comp _ r m _ _
  let w' := cF.obj (Over.mk v')
  -- the first component of `w'` is `r'`, up to the identification of its source
  have hw'x : ∃ h : (w'.x : Over T').left = V', (w'.x : Over T').hom = eqToHom h ≫ r' := by
    have h₂ : (Over.forget T').IsHomLift (𝟙 V') (e.inv.hom.app (Over.mk v')) :=
      e.inv.hom.isHomLift' (Over.mk v')
    have hw : (Over.forget T').map (e.inv.hom.app (Over.mk v')) ≫ (w'.x : Over T').hom =
        v' ≫ q := Over.w (e.inv.hom.app (Over.mk v'))
    have hfac := @IsHomLift.fac' _ _ _ _ (Over.forget T') _ _ _ _ (𝟙 V')
      (e.inv.hom.app (Over.mk v')) h₂
    rw [hfac, hv'q] at hw
    refine ⟨@IsHomLift.codomain_eq _ _ _ _ (Over.forget T') _ _ _ _ (𝟙 V')
      (e.inv.hom.app (Over.mk v')) h₂, ?_⟩
    rw [← hw]
    have key : ∀ {A : BigFppfOver B S hS} (h₁ : A = V') (h₀ : V' = V') (h₃ : V' = A)
        (g : A ⟶ T'), g = eqToHom h₁ ≫ (eqToHom h₀ ≫ 𝟙 V' ≫ eqToHom h₃) ≫ g := by
      intro A h₁ h₀ h₃ g
      subst h₁
      simp
    exact key _ _ _ _
  obtain ⟨hw'l, hw'h⟩ := hw'x
  have hψw' : 𝒳.val.val.p.IsHomLift r' (ψ w') := by
    have hc : 𝒳.val.val.p.IsHomLift (w'.x : Over T').hom
        (TwoFibreProductOver.TwoYonedaPair.chosenHom hX y w'.x) :=
      (Functor.TwoYoneda.chosenLift 𝒳.val.val.p hX T' y w'.x).isStronglyCartesian.toIsHomLift
    have hc' : 𝒳.val.val.p.IsHomLift r'
        (TwoFibreProductOver.TwoYonedaPair.chosenHom hX y w'.x) := by
      rw [hw'h] at hc
      exact (IsHomLift.lift_eqToHom_comp_iff _ _ _ _).1 hc
    have hv : 𝒳.val.val.p.IsHomLift (𝟙 w'.base) w'.iso.hom := w'.vertical
    have hinv : 𝒳.val.val.p.IsHomLift (𝟙 w'.base) w'.iso.inv := inferInstance
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒳.val.val.p _ _ _ w'.base w'.iso.inv hinv _ _ r'
      _ hc'
  refine ⟨sndF.obj (cF.obj (Over.mk (j ≫ v'))), sndF.obj w', sndF.map A, sndF.map N, ψ w',
    BasedFunctor.preserves_isHomLift (F := sndF) (f := j) (φ := A),
    BasedFunctor.preserves_isHomLift (F := sndF) (f := r ≫ m) (φ := N), hψw', ?_⟩
  rw [hψ A, ← hψs]
  exact (hψ N).symm

end AlgebraicGeometry.Stack

end
