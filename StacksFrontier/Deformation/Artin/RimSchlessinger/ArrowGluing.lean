module

public import StacksFrontier.Deformation.Artin.RimSchlessinger.FibreProductLift
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso

/-!
# Gluing arrows through a full comparison functor

Let `p : 𝒳 ⥤ 𝒞` be fibred in groupoids with a choice of pullbacks, and let
`f : U ⟶ V`, `g : U ⟶ W`, `i : V ⟶ Z`, `j : W ⟶ Z` be a commutative square of `𝒞` whose
comparison functor `𝒳_Z ⥤ 𝒳_V ×_{𝒳_U} 𝒳_W` (`Deformation.Artin.fiberSquareComparison`) is full.
Then an arrow out of an object `e` over `Z` can be glued from arrows out of restrictions of `e`
to `V` and to `W` which agree on the restriction to `U`.

This is the half of the Rim–Schlessinger condition which produces morphisms rather than
objects: condition (RS*) makes the comparison functor an equivalence, in particular full.

## Main results

* `Deformation.Artin.exists_glued_arrow_of_fiberSquareComparison_full`: the gluing of arrows.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace Deformation.Artin

universe u₁ v₁ u₂ v₂

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Limits.CategoricalPullback.π₁
  CategoryTheory.Limits.CategoricalPullback.π₂

variable {C : Type u₁} [Category.{v₁} C] {F : Type u₂} [Category.{v₂} F]

/-- The comparison isomorphism of `fiberSquareComparison` is compatible with the chosen
cartesian arrows to the object over the fourth corner. -/
@[reassoc]
theorem fiberSquareComparison_iso_hom_fac
    (p : F ⥤ C) (c : p.ChoiceOfPullbacks)
    {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (h : f ≫ i = g ≫ j) (z : p.Fiber Z) :
    Functor.Fiber.fiberInclusion.map
        ((fiberSquareComparison p c f g i j h).obj z).iso.hom ≫
      c.map g (c.obj j z) ≫ c.map j z = c.map f (c.obj i z) ≫ c.map i z := by
  have heq : ∀ {f₁ f₂ : U ⟶ Z} (e : f₁ = f₂) (x : p.Fiber Z),
      Functor.Fiber.fiberInclusion.map ((eqToHom (congrArg c.pullbackFunctor e)).app x) ≫
        c.map f₂ x = c.map f₁ x := by
    rintro _ _ rfl x
    simp
  change Functor.Fiber.fiberInclusion.map
    ((c.objCompIso f i z).inv ≫
      (eqToHom (congrArg c.pullbackFunctor h)).app z ≫ (c.objCompIso g j z).hom) ≫
        c.map g (c.obj j z) ≫ c.map j z = _
  simp only [Functor.map_comp, Category.assoc, Functor.ChoiceOfPullbacks.objCompIso_hom_fac]
  rw [heq h z]
  exact Functor.fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- One leg of the gluing of arrows: an arrow `rV` that is strongly cartesian over `i` is
identified with the chosen restriction of `eZ`, and an arrow `βV` out of its source lying over
`i ≫ gZ` induces a fibre morphism between the restrictions of `eZ` and of the chosen
restriction of `t` along `gZ`. -/
private theorem exists_fiber_iso_and_hom_of_isStronglyCartesian
    {p : F ⥤ C} (c : p.ChoiceOfPullbacks) {V Z : C} (i : V ⟶ Z) (eZ : p.Fiber Z)
    {xV t : F} (rV : xV ⟶ eZ.1) [p.IsStronglyCartesian i rV] (gZ : Z ⟶ p.obj t) (βV : xV ⟶ t)
    [p.IsHomLift (i ≫ gZ) βV] :
    ∃ (eV : c.obj i eZ ≅ (⟨xV, IsHomLift.domain_eq p i rV⟩ : p.Fiber V))
      (φ : c.obj i eZ ⟶ c.obj i (c.obj gZ ⟨t, rfl⟩)),
      Fiber.fiberInclusion.map eV.hom ≫ rV = c.map i eZ ∧
      Fiber.fiberInclusion.map φ ≫ c.map i (c.obj gZ ⟨t, rfl⟩) ≫ c.map gZ ⟨t, rfl⟩ =
        Fiber.fiberInclusion.map eV.hom ≫ βV ∧
      ∀ βt : eZ ⟶ c.obj gZ ⟨t, rfl⟩, c.homMap i βt = φ →
        rV ≫ Fiber.fiberInclusion.map βt ≫ c.map gZ ⟨t, rfl⟩ = βV := by
  have hκ : p.IsStronglyCartesian gZ (c.map gZ ⟨t, rfl⟩) := c.isStronglyCartesian gZ _
  let eV : c.obj i eZ ≅ (⟨xV, IsHomLift.domain_eq p i rV⟩ : p.Fiber V) :=
    fiberIsoOfCartesian i (c.map i eZ) rV inferInstance inferInstance
  have heV : Fiber.fiberInclusion.map eV.hom ≫ rV = c.map i eZ :=
    fiberIsoOfCartesian_hom_fac _ _ _ _ _
  let φ : c.obj i eZ ⟶ c.obj i (c.obj gZ ⟨t, rfl⟩) :=
    ⟨IsStronglyCartesian.map p (i ≫ gZ) (c.map i (c.obj gZ ⟨t, rfl⟩) ≫ c.map gZ ⟨t, rfl⟩)
      (Category.id_comp (i ≫ gZ)).symm (Fiber.fiberInclusion.map eV.hom ≫ βV), inferInstance⟩
  have hφ : Fiber.fiberInclusion.map φ ≫ c.map i (c.obj gZ ⟨t, rfl⟩) ≫ c.map gZ ⟨t, rfl⟩ =
      Fiber.fiberInclusion.map eV.hom ≫ βV :=
    IsStronglyCartesian.fac p (i ≫ gZ) _ (Category.id_comp (i ≫ gZ)).symm
      (Fiber.fiberInclusion.map eV.hom ≫ βV)
  refine ⟨eV, φ, heV, hφ, fun βt hβt => ?_⟩
  rw [← cancel_epi (Fiber.fiberInclusion.map eV.hom), ← Category.assoc, heV,
    ← Category.assoc, ← Functor.ChoiceOfPullbacks.homMap_fac, hβt, Category.assoc, hφ]

/-- **Gluing arrows.** If the comparison functor of a commutative square of the base is full,
an arrow out of an object `e` over the fourth corner, lying over a prescribed `gZ`, can be
glued from arrows `βV`, `βW` out of objects `xV`, `xW` mapping to `e` over the two legs of the
square, as soon as `βV` and `βW` agree on an object `xU` mapping to both over the other two
legs. -/
theorem exists_glued_arrow_of_fiberSquareComparison_full
    (p : F ⥤ C) (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
    {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    [(fiberSquareComparison p c f g i j h).Full]
    {e t xU xV xW : F} (he : p.obj e = Z) (gZ : Z ⟶ p.obj t)
    (rV : xV ⟶ e) (rW : xW ⟶ e) (sV : xU ⟶ xV) (sW : xU ⟶ xW)
    [p.IsHomLift i rV] [p.IsHomLift j rW] [p.IsHomLift f sV] [p.IsHomLift g sW]
    (hs : sV ≫ rV = sW ≫ rW)
    (βV : xV ⟶ t) (βW : xW ⟶ t) [p.IsHomLift (i ≫ gZ) βV] [p.IsHomLift (j ≫ gZ) βW]
    (hβ : sV ≫ βV = sW ≫ βW) :
    ∃ β : e ⟶ t, p.IsHomLift gZ β ∧ rV ≫ β = βV ∧ rW ≫ β = βW := by
  let E := fiberSquareComparison p c f g i j h
  let eZ : p.Fiber Z := ⟨e, he⟩
  let t' : p.Fiber Z := c.obj gZ ⟨t, rfl⟩
  let κ : t'.1 ⟶ t := c.map gZ ⟨t, rfl⟩
  have hκ : p.IsStronglyCartesian gZ κ := c.isStronglyCartesian gZ _
  have hrV : p.IsStronglyCartesian i rV := hp.isStronglyCartesian_homLift i rV
  have hrW : p.IsStronglyCartesian j rW := hp.isStronglyCartesian_homLift j rW
  have hsV : p.IsStronglyCartesian f sV := hp.isStronglyCartesian_homLift f sV
  have hsW : p.IsStronglyCartesian g sW := hp.isStronglyCartesian_homLift g sW
  -- the restrictions of `e` compared with `xV` and `xW`, and the induced maps to `t'`
  obtain ⟨eV, φV, heV, hφV, hV⟩ := exists_fiber_iso_and_hom_of_isStronglyCartesian c i eZ rV gZ βV
  obtain ⟨eW, φW, heW, hφW, hW⟩ := exists_fiber_iso_and_hom_of_isStronglyCartesian c j eZ rW gZ βW
  -- the comparison of the restriction of `e` to `U` with `xU`
  let xUf : p.Fiber U := ⟨xU, IsHomLift.domain_eq p f sV⟩
  let eU : c.obj f (c.obj i eZ) ≅ xUf :=
    fiberIsoOfCartesian f (c.map f (c.obj i eZ) ≫ Fiber.fiberInclusion.map eV.hom) sV
      (by
        have : p.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map eV.hom) := eV.hom.2
        have : p.IsStronglyCartesian (𝟙 V) (Fiber.fiberInclusion.map eV.hom) :=
          hp.isStronglyCartesian_homLift _ _
        simpa using (inferInstance : p.IsCartesian (f ≫ 𝟙 V)
          (c.map f (c.obj i eZ) ≫ Fiber.fiberInclusion.map eV.hom)))
      inferInstance
  have heU : Fiber.fiberInclusion.map eU.hom ≫ sV =
      c.map f (c.obj i eZ) ≫ Fiber.fiberInclusion.map eV.hom :=
    fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have heUW : Fiber.fiberInclusion.map eU.hom ≫ sW =
      Fiber.fiberInclusion.map (E.obj eZ).iso.hom ≫ c.map g (c.obj j eZ) ≫
        Fiber.fiberInclusion.map eW.hom := by
    refine IsStronglyCartesian.ext p j rW g ?_
    rw [Category.assoc, ← hs, ← Category.assoc, heU, Category.assoc, heV, Category.assoc,
      Category.assoc, heW, fiberSquareComparison_iso_hom_fac]
  -- the morphism of the two-fibre product
  let φ : E.obj eZ ⟶ E.obj t' :=
    { fst := φV
      snd := φW
      w := by
        refine fiber_hom_ext_of_cartesian (g ≫ j ≫ gZ)
          (c.map g (c.obj j t') ≫ c.map j t' ≫ κ) inferInstance _ _ ?_
        change Fiber.fiberInclusion.map (c.homMap f φV ≫ (E.obj t').iso.hom) ≫ _ =
          Fiber.fiberInclusion.map ((E.obj eZ).iso.hom ≫ c.homMap g φW) ≫ _
        simp only [Functor.map_comp, Category.assoc]
        rw [fiberSquareComparison_iso_hom_fac_assoc, Functor.ChoiceOfPullbacks.homMap_fac_assoc,
          Functor.ChoiceOfPullbacks.homMap_fac_assoc, hφV, hφW, ← Category.assoc (c.map f _),
          ← heU, ← Category.assoc (c.map g _), ← Category.assoc, ← Category.assoc,
          Category.assoc, hβ, ← Category.assoc]
        exact congrArg (· ≫ βW) (heUW.trans (Category.assoc _ _ _).symm) }
  obtain ⟨βt, hβt⟩ : ∃ βt : eZ ⟶ t', E.map βt = φ := ⟨E.preimage φ, E.map_preimage φ⟩
  have hfst : c.homMap i βt = φV := congrArg CategoricalPullback.Hom.fst hβt
  have hsnd : c.homMap j βt = φW := congrArg CategoricalPullback.Hom.snd hβt
  exact ⟨Fiber.fiberInclusion.map βt ≫ κ, inferInstance, hV βt hfst, hW βt hsnd⟩

/-- **Gluing objects.** If the comparison functor of a commutative square of the base is
essentially surjective, objects over the second and third corners with arrows from a common
object over the first corner glue to an object over the fourth corner. -/
theorem exists_glued_object_of_fiberSquareComparison_essSurj
    (p : F ⥤ C) (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
    {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    [(fiberSquareComparison p c f g i j h).EssSurj]
    {xU xV xW : F} (hxV : p.obj xV = V) (hxW : p.obj xW = W)
    (sV : xU ⟶ xV) (sW : xU ⟶ xW) [p.IsHomLift f sV] [p.IsHomLift g sW] :
    ∃ (e : F) (_ : p.obj e = Z) (rV : xV ⟶ e) (rW : xW ⟶ e),
      p.IsHomLift i rV ∧ p.IsHomLift j rW ∧ sV ≫ rV = sW ≫ rW := by
  have hsV : p.IsStronglyCartesian f sV := hp.isStronglyCartesian_homLift f sV
  have hsW : p.IsStronglyCartesian g sW := hp.isStronglyCartesian_homLift g sW
  let xVf : p.Fiber V := ⟨xV, hxV⟩
  let xWf : p.Fiber W := ⟨xW, hxW⟩
  let xUf : p.Fiber U := ⟨xU, IsHomLift.domain_eq p f sV⟩
  let ea : c.obj f xVf ≅ xUf := fiberIsoOfCartesian f (c.map f xVf) sV inferInstance inferInstance
  let eb : xUf ≅ c.obj g xWf := fiberIsoOfCartesian g sW (c.map g xWf) inferInstance inferInstance
  obtain ⟨z, ex, ey, hcomp⟩ :=
    exists_fiber_of_fiberSquareComparison_essSurj p c f g i j h xVf xWf (ea ≪≫ eb)
  let rV : xV ⟶ z.1 := Fiber.fiberInclusion.map ex.inv ≫ c.map i z
  let rW : xW ⟶ z.1 := Fiber.fiberInclusion.map ey.inv ≫ c.map j z
  refine ⟨z.1, z.2, rV, rW, inferInstance, inferInstance, ?_⟩
  have hea : Fiber.fiberInclusion.map ea.hom ≫ sV = c.map f xVf :=
    fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have heb : Fiber.fiberInclusion.map eb.hom ≫ c.map g xWf = sW :=
    fiberIsoOfCartesian_hom_fac _ _ _ _ _
  have hX : (ea ≪≫ eb).hom = ((c.pullbackFunctor f).mapIso ex).inv ≫
      ((fiberSquareComparison p c f g i j h).obj z).iso.hom ≫
        (c.pullbackFunctor g).map ey.hom := (Iso.eq_inv_comp _).mpr hcomp
  have hX' := congrArg Fiber.fiberInclusion.map hX
  simp only [Iso.trans_hom, Functor.map_comp, Functor.mapIso_inv] at hX'
  rw [← cancel_epi (Fiber.fiberInclusion.map ea.hom), ← Category.assoc, hea, ← heb]
  simp only [Category.assoc]
  rw [← Category.assoc (Fiber.fiberInclusion.map ea.hom), hX']
  simp only [rV, rW, Category.assoc, Functor.ChoiceOfPullbacks.pullbackFunctor_map,
    Functor.ChoiceOfPullbacks.homMap_fac_assoc]
  rw [← Category.assoc (Fiber.fiberInclusion.map ey.hom), ← Functor.map_comp, ey.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  calc _ = Fiber.fiberInclusion.map (c.homMap f ex.inv) ≫ c.map f (c.obj i z) ≫ c.map i z :=
        (c.homMap_fac_assoc f ex.inv (c.map i z)).symm
    _ = _ := by
      rw [← fiberSquareComparison_iso_hom_fac p c f g i j h z]
      rfl

/-- A morphism `i` over `l ≫ incl` which factors as `r ≫ π` through a strongly cartesian
arrow `π` over `incl` also factors through the lift `τ` of the identity along a section `ρ`
of `incl`. -/
theorem exists_comp_eq_of_isStronglyCartesian_of_retraction (p : F ⥤ C)
    {A D Bs : C} (l : A ⟶ D) (incl : D ⟶ Bs) (ρ : Bs ⟶ D) (hρ : ρ ≫ incl = 𝟙 Bs)
    (hρl : l ≫ incl ≫ ρ = l) {y z zD : F} (π : zD ⟶ z) [p.IsStronglyCartesian incl π]
    (hz : p.obj z = Bs) (i : y ⟶ z) [p.IsHomLift (l ≫ incl) i] (r : y ⟶ zD)
    [p.IsHomLift l r] (hr : r ≫ π = i) :
    ∃ τ : z ⟶ zD, τ ≫ π = 𝟙 z ∧ i ≫ τ = r := by
  have : p.IsHomLift (𝟙 Bs) (𝟙 z) := hz ▸ inferInstance
  let τ : z ⟶ zD := IsStronglyCartesian.map p incl π hρ.symm (𝟙 z)
  have hτ : τ ≫ π = 𝟙 z := IsStronglyCartesian.fac p incl π hρ.symm (𝟙 z)
  have : p.IsHomLift ρ τ := by
    simp only [τ]
    infer_instance
  refine ⟨τ, hτ, ?_⟩
  have : p.IsHomLift l (i ≫ τ) := by
    rw [show l = (l ≫ incl) ≫ ρ by rw [Category.assoc, hρl]]
    infer_instance
  refine IsStronglyCartesian.ext p incl π l ?_
  rw [Category.assoc, hτ, Category.comp_id, hr]

/-! ### Descending a lift along a retracted square-zero pushout -/

section Retract

open AlgebraicGeometry

universe u v w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Descending a lift through a retraction.** Let `𝒳` satisfy (RS*), and let

* `gA : A'' ⟶ A`, `j : A'' ⟶ B''`, `lA : A ⟶ D`, `lB : B'' ⟶ D` be a commutative square of
  affine objects of the site meeting the hypotheses of (RS*) (a fibre product on global
  sections, with `j` a square-zero thickening),
* `incl : D ⟶ Bs` a morphism with a section `ρ : Bs ⟶ D`, such that `fA := lA ≫ incl` and
  `gB := lB ≫ incl` satisfy `fA ≫ ρ = lA`,
* every pair of morphisms out of `B''` and `A` agreeing on `A''` glue to one out of `D`.

Let `i : y ⟶ z` lie over `fA`, let `a : y ⟶ x`, and let `i'' : y'' ⟶ z''` be a restriction of
`i` along `gB` and `gA`. If the restricted lifting problem has a solution `b'' : z'' ⟶ x`, then so
does the original one. -/
theorem exists_lift_of_lift_after_retract
    {F : Type v} [Category.{w} F] (p : F ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (hRS : SatisfiesRSStar B S hS p hp)
    {A A'' B'' D Bs : BigAffineFppf B S hS}
    (gA : A'' ⟶ A) (j : A'' ⟶ B'') (lA : A ⟶ D) (lB : B'' ⟶ D) (hsq : gA ≫ lA = j ≫ lB)
    (hpb : IsPullback ((BigAffineFppf.toScheme B S hS).map lA).appTop
      ((BigAffineFppf.toScheme B S hS).map lB).appTop
      ((BigAffineFppf.toScheme B S hS).map gA).appTop
      ((BigAffineFppf.toScheme B S hS).map j).appTop)
    (hsurj : Function.Surjective ((BigAffineFppf.toScheme B S hS).map j).appTop.hom)
    (hker : RingHom.ker ((BigAffineFppf.toScheme B S hS).map j).appTop.hom ^ 2 = ⊥)
    (incl : D ⟶ Bs) (ρ : Bs ⟶ D) (hρ : ρ ≫ incl = 𝟙 Bs) (hρA : lA ≫ incl ≫ ρ = lA)
    {x y z y'' z'' : F}
    (hpush : ∀ (g₁ : B''.obj ⟶ p.obj x) (g₂ : A.obj ⟶ p.obj x), j.hom ≫ g₁ = gA.hom ≫ g₂ →
      ∃ g : D.obj ⟶ p.obj x, lB.hom ≫ g = g₁ ∧ lA.hom ≫ g = g₂)
    (i : y ⟶ z) [p.IsHomLift (lA ≫ incl).hom i] (a : y ⟶ x)
    (pz : z'' ⟶ z) [p.IsHomLift (lB ≫ incl).hom pz]
    (py : y'' ⟶ y) [p.IsHomLift gA.hom py]
    (i'' : y'' ⟶ z'') [p.IsHomLift j.hom i''] (hcomm : i'' ≫ pz = py ≫ i)
    (b'' : z'' ⟶ x) (hb'' : i'' ≫ b'' = py ≫ a) :
    ∃ b : z ⟶ x, i ≫ b = a := by
  classical
  have : p.IsFibered := hp.isFibered
  let ι := BigAffineFppf.inclusion B S hS
  have hyA : p.obj y = A.obj := IsHomLift.domain_eq p (lA ≫ incl).hom i
  have hzB : p.obj z = Bs.obj := IsHomLift.codomain_eq p (lA ≫ incl).hom i
  have hz''B : p.obj z'' = B''.obj := IsHomLift.domain_eq p (lB ≫ incl).hom pz
  -- the base maps of `a` and `b''`
  let a₀ : A.obj ⟶ p.obj x := eqToHom hyA.symm ≫ p.map a
  let g'' : B''.obj ⟶ p.obj x := eqToHom hz''B.symm ≫ p.map b''
  have ha : p.IsHomLift a₀ a := IsHomLift.of_fac' p a₀ a hyA rfl (by simp [a₀])
  have hb : p.IsHomLift g'' b'' := IsHomLift.of_fac' p g'' b'' hz''B rfl (by simp [g''])
  have hglue : j.hom ≫ g'' = gA.hom ≫ a₀ := by
    have h1 : p.IsHomLift (j.hom ≫ g'') (i'' ≫ b'') := inferInstance
    rw [hb''] at h1
    rw [IsHomLift.fac p (j.hom ≫ g'') (py ≫ a), IsHomLift.fac p (gA.hom ≫ a₀) (py ≫ a)]
  obtain ⟨gD, hgDB, hgDA⟩ := hpush g'' a₀ hglue
  -- the restriction of `z` to `D`
  obtain ⟨zD, πD, hπD⟩ := hp.exists_lift incl.hom z hzB
  have hπDc : p.IsStronglyCartesian incl.hom πD := hp.isStronglyCartesian_homLift _ _
  have hfA : (lA ≫ incl).hom = lA.hom ≫ incl.hom := rfl
  have hgB : (lB ≫ incl).hom = lB.hom ≫ incl.hom := rfl
  let rV : y ⟶ zD := IsStronglyCartesian.map p incl.hom πD hfA i
  let rW : z'' ⟶ zD := IsStronglyCartesian.map p incl.hom πD hgB pz
  have hrV : rV ≫ πD = i := IsStronglyCartesian.fac p incl.hom πD hfA i
  have hrW : rW ≫ πD = pz := IsStronglyCartesian.fac p incl.hom πD hgB pz
  have hrVl : p.IsHomLift lA.hom rV := by
    simp only [rV]
    infer_instance
  have hrWl : p.IsHomLift lB.hom rW := by
    simp only [rW]
    infer_instance
  have hs : py ≫ rV = i'' ≫ rW := by
    have h2 : p.IsHomLift (gA.hom ≫ lA.hom) (i'' ≫ rW) := by
      have : gA.hom ≫ lA.hom = j.hom ≫ lB.hom := congrArg (fun m => m.hom) hsq
      rw [this]
      infer_instance
    refine IsStronglyCartesian.ext p incl.hom πD (gA.hom ≫ lA.hom) ?_
    rw [Category.assoc, Category.assoc, hrV, hrW, hcomm]
  have := hRS A'' A B'' D gA j lA lB hsq hpb hsurj hker
  have : (fiberSquareComparison p (Functor.chosenPullbacks p) (ι.map gA) (ι.map j)
      (ι.map lA) (ι.map lB) (by simpa only [Functor.map_comp] using congrArg ι.map hsq)).Full :=
    inferInstance
  have : p.IsHomLift (ι.map lA) rV := hrVl
  have : p.IsHomLift (ι.map lB) rW := hrWl
  have : p.IsHomLift (ι.map gA) py := (inferInstance : p.IsHomLift gA.hom py)
  have : p.IsHomLift (ι.map j) i'' := (inferInstance : p.IsHomLift j.hom i'')
  have : p.IsHomLift (ι.map lA ≫ gD) a := (by rwa [hgDA] : p.IsHomLift (lA.hom ≫ gD) a)
  have : p.IsHomLift (ι.map lB ≫ gD) b'' := (by rwa [hgDB] : p.IsHomLift (lB.hom ≫ gD) b'')
  obtain ⟨β, hβl, hβV', hβW'⟩ := exists_glued_arrow_of_fiberSquareComparison_full p hp
    (Functor.chosenPullbacks p) (ι.map gA) (ι.map j) (ι.map lA) (ι.map lB)
    (congrArg (fun m => m.hom) hsq) (IsHomLift.domain_eq p incl.hom πD) gD rV rW py i'' hs
    a b'' hb''.symm
  -- pull back along the retraction
  have : p.IsHomLift (lA.hom ≫ incl.hom) i := (inferInstance : p.IsHomLift (lA ≫ incl).hom i)
  obtain ⟨τ, -, hiτ⟩ := exists_comp_eq_of_isStronglyCartesian_of_retraction p lA.hom incl.hom
    ρ.hom (congrArg (fun m => m.hom) hρ) (congrArg (fun m => m.hom) hρA) πD hzB i rV hrV
  exact ⟨τ ≫ β, by rw [← Category.assoc, hiτ, hβV']⟩

end Retract

end Deformation.Artin
