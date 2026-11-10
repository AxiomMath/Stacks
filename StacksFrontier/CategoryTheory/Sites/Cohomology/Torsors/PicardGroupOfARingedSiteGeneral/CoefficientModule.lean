module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSiteGeneral.GeneratorTorsor

/-!
# The module attached to a unit torsor, with independent universes

The module attached to a torsor under the units of a ringed site
`AlgebraicGeometry.RingedSite.{u, v, w}`: the unit between two sections of a torsor, the
coefficient generator, the shrinking of the attached module to the universe of the sections on an
essentially small site and the isomorphism of its generator torsor with the given torsor, and
the generator torsors of isomorphic modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite MonoidalCategory

universe u v w t

namespace Stacks.Cohomology.Torsors.Generators

/-! ### The module attached to a torsor under the units -/

/-- The unique unit carrying one section of a torsor to another.

This generalizes `Stacks.Cohomology.Torsors.Generators.torsorUnitBetween`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def torsorUnitBetween' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.Cᵒᵖ)
    (s t : F.1.presheaf.obj U) : (X.O.obj.obj U)ˣ :=
  Additive.toMul (Multiplicative.toAdd (F.1.simplyTransitive U ⟨s⟩ s t).choose)

/-- The defining property of `torsorUnitBetween'`.

This generalizes `Stacks.Cohomology.Torsors.Generators.torsorUnitBetween_act`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem torsorUnitBetween_act' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.Cᵒᵖ)
    (s t : F.1.presheaf.obj U) :
    F.1.act U (Multiplicative.ofAdd (Additive.ofMul (torsorUnitBetween' X F U s t))) s = t :=
  (F.1.simplyTransitive U ⟨s⟩ s t).choose_spec.1

/-- `torsorUnitBetween'` is the unique unit with that property.

This generalizes `Stacks.Cohomology.Torsors.Generators.torsorUnitBetween_eq`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem torsorUnitBetween_eq' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.Cᵒᵖ)
    (s t : F.1.presheaf.obj U) (a : (X.O.obj.obj U)ˣ)
    (ha : F.1.act U (Multiplicative.ofAdd (Additive.ofMul a)) s = t) :
    torsorUnitBetween' X F U s t = a :=
  congrArg (fun b => Additive.toMul (Multiplicative.toAdd b))
    ((F.1.simplyTransitive U ⟨s⟩ s t).choose_spec.2 _ ha).symm

/-- A section is carried to itself by the unit one.

This generalizes `Stacks.Cohomology.Torsors.Generators.torsorUnitBetween_self`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem torsorUnitBetween_self' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.Cᵒᵖ)
    (s : F.1.presheaf.obj U) : torsorUnitBetween' X F U s s = 1 :=
  torsorUnitBetween_eq' X F U s s 1 (F.1.one_act U s)

/-- `torsorUnitBetween'` is compatible with restriction.

This generalizes `Stacks.Cohomology.Torsors.Generators.torsorUnitBetween_naturality`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem torsorUnitBetween_naturality' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X))
    {U V : X.Cᵒᵖ} (f : U ⟶ V) (s t : F.1.presheaf.obj U) :
    torsorUnitBetween' X F V (F.1.presheaf.map f s) (F.1.presheaf.map f t) =
      Units.map (X.O.obj.map f).hom.toMonoidHom (torsorUnitBetween' X F U s t) := by
  apply torsorUnitBetween_eq'
  exact (F.1.naturality f _ s).symm.trans
    (congrArg (fun z => F.1.presheaf.map f z) (torsorUnitBetween_act' X F U s t))

/-- Translating the source divides `torsorUnitBetween'` by the translating unit.

This generalizes `Stacks.Cohomology.Torsors.Generators.torsorUnitBetween_act_left`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem torsorUnitBetween_act_left' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.Cᵒᵖ)
    (s t : F.1.presheaf.obj U) (a : (X.O.obj.obj U)ˣ) :
    torsorUnitBetween' X F U (F.1.act U (Multiplicative.ofAdd (Additive.ofMul a)) s) t =
      a⁻¹ * torsorUnitBetween' X F U s t := by
  apply torsorUnitBetween_eq'
  have h : Multiplicative.ofAdd (Additive.ofMul (a⁻¹ * torsorUnitBetween' X F U s t)) *
      Multiplicative.ofAdd (Additive.ofMul a) =
      Multiplicative.ofAdd (Additive.ofMul (torsorUnitBetween' X F U s t)) := by
    change Multiplicative.ofAdd (Additive.ofMul
      ((a⁻¹ * torsorUnitBetween' X F U s t) * a)) = _
    congr 2
    simp [mul_comm]
  have h1 := F.1.mul_act U
    (Multiplicative.ofAdd (Additive.ofMul (a⁻¹ * torsorUnitBetween' X F U s t)))
    (Multiplicative.ofAdd (Additive.ofMul a)) s
  exact h1.symm.trans
    ((congrArg (fun g => F.1.act U g s) h).trans (torsorUnitBetween_act' X F U s t))

/-- Translating the target multiplies `torsorUnitBetween'` by the translating unit.

This generalizes `Stacks.Cohomology.Torsors.Generators.torsorUnitBetween_act_right`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem torsorUnitBetween_act_right' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.Cᵒᵖ)
    (s t : F.1.presheaf.obj U) (a : (X.O.obj.obj U)ˣ) :
    torsorUnitBetween' X F U s (F.1.act U (Multiplicative.ofAdd (Additive.ofMul a)) t) =
      a * torsorUnitBetween' X F U s t := by
  apply torsorUnitBetween_eq'
  have h0 : Multiplicative.ofAdd (Additive.ofMul (a * torsorUnitBetween' X F U s t)) =
      Multiplicative.ofAdd (Additive.ofMul a) *
        Multiplicative.ofAdd (Additive.ofMul (torsorUnitBetween' X F U s t)) := rfl
  have h1 := F.1.mul_act U (Multiplicative.ofAdd (Additive.ofMul a))
    (Multiplicative.ofAdd (Additive.ofMul (torsorUnitBetween' X F U s t))) s
  exact (congrArg (fun g => F.1.act U g s) h0).trans (h1.trans
    (congrArg (fun z => F.1.act U (Multiplicative.ofAdd (Additive.ofMul a)) z)
      (torsorUnitBetween_act' X F U s t)))

attribute [local instance] coefficientFamilyModule'

/-- A section of the torsor over `U` gives a coefficient section over `U`: the unit carrying a
given section to the restriction of the chosen one.

This generalizes `Stacks.Cohomology.Torsors.Generators.coefficientGenerator`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def coefficientGenerator' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C)
    (s : F.1.presheaf.obj (op U)) : CoefficientSection' X F U := by
  refine ⟨fun V t => (torsorUnitBetween' X F (op V.left) t (F.1.presheaf.map V.hom.op s)).val,
    ?_, ?_⟩
  · intro V W f t
    have h : F.1.presheaf.map f.left.op (F.1.presheaf.map V.hom.op s) =
        F.1.presheaf.map W.hom.op s := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Over.w f]
    change (torsorUnitBetween' X F (op W.left) (F.1.presheaf.map f.left.op t)
      (F.1.presheaf.map W.hom.op s)).val = _
    calc
      _ = (torsorUnitBetween' X F (op W.left) (F.1.presheaf.map f.left.op t)
          (F.1.presheaf.map f.left.op (F.1.presheaf.map V.hom.op s))).val :=
        congrArg (fun z => (torsorUnitBetween' X F (op W.left)
          (F.1.presheaf.map f.left.op t) z).val) h.symm
      _ = _ := congrArg Units.val
        (torsorUnitBetween_naturality' X F f.left.op t (F.1.presheaf.map V.hom.op s))
  · intro V g t
    exact congrArg Units.val
      (torsorUnitBetween_act_left' X F (op V.left) t (F.1.presheaf.map V.hom.op s) g)

/-- `coefficientGenerator'` is compatible with restriction.

This generalizes `Stacks.Cohomology.Torsors.Generators.coefficientGenerator_restrict`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem coefficientGenerator_restrict' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X))
    {U V : X.C} (f : V ⟶ U) (s : F.1.presheaf.obj (op U)) :
    coefficientSectionRestrict' X F f (coefficientGenerator' X F U s) =
      coefficientGenerator' X F V (F.1.presheaf.map f.op s) := by
  apply Subtype.ext
  funext W t
  change (torsorUnitBetween' X F _ t (F.1.presheaf.map (W.hom ≫ f).op s)).val =
    (torsorUnitBetween' X F _ t (F.1.presheaf.map W.hom.op (F.1.presheaf.map f.op s))).val
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Every coefficient section is a multiple of the one attached to a section of the torsor.

This generalizes `Stacks.Cohomology.Torsors.Generators.coefficientSection_eq_smul_generator`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem coefficientSection_eq_smul_generator' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C)
    (s : F.1.presheaf.obj (op U)) (a : CoefficientSection' X F U) :
    a = a.val (Over.mk (𝟙 U)) s • coefficientGenerator' X F U s := by
  apply Subtype.ext
  funext V t
  let sV := F.1.presheaf.map V.hom.op s
  let q := torsorUnitBetween' X F (op V.left) t sV
  have he := a.property.2 V q t
  rw [torsorUnitBetween_act'] at he
  have hn := a.property.1 (Over.mk (𝟙 U)) V (Over.homMk V.hom) s
  change a.val V sV = (X.O.obj.map V.hom.op) (a.val (Over.mk (𝟙 U)) s) at hn
  change a.val V t = (X.O.obj.map V.hom.op) (a.val (Over.mk (𝟙 U)) s) * q.val
  calc
    a.val V t = q.val * ((q⁻¹).val * a.val V t) := by simp
    _ = q.val * a.val V sV := congrArg (q.val * ·) he.symm
    _ = q.val * (X.O.obj.map V.hom.op) (a.val (Over.mk (𝟙 U)) s) := by rw [hn]
    _ = _ := mul_comm _ _

/-- Multiplication by the coefficient section attached to a section of the torsor is
bijective.

This generalizes `Stacks.Cohomology.Torsors.Generators.coefficientGenerator_bijective`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem coefficientGenerator_bijective' (X : RingedSite.{u, v, w})
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X)) (U : X.C)
    (s : F.1.presheaf.obj (op U)) :
    Function.Bijective (fun r : X.O.obj.obj (op U) => r • coefficientGenerator' X F U s) := by
  constructor
  · intro r t h
    have he := congrArg (fun a : CoefficientSection' X F U => a.val (Over.mk (𝟙 U)) s) h
    change (X.O.obj.map (𝟙 U).op) r *
        (torsorUnitBetween' X F (op U) s (F.1.presheaf.map (𝟙 U).op s)).val =
      (X.O.obj.map (𝟙 U).op) t *
        (torsorUnitBetween' X F (op U) s (F.1.presheaf.map (𝟙 U).op s)).val at he
    simpa [torsorUnitBetween_self'] using he
  · intro a
    exact ⟨a.val (Over.mk (𝟙 U)) s, (coefficientSection_eq_smul_generator' X F U s a).symm⟩

/-! ### Shrinking the attached module to the universe of the sections

A coefficient section over `U` is a family indexed by the slice `X.C/U`, so the sections of
`coefficientSheafLarge` live in `Type (max u v w)`, whereas a sheaf of modules on `X` has its
sections in `Type w`. On a site that is essentially `w`-small the raise is an artefact of the
construction: a coefficient section is compatible with restriction and the structure morphism of
an isomorphism of the slice is an isomorphism, so a coefficient section is determined by its
components on a `w`-small model of the slice. The attached module is therefore sectionwise
`w`-small, and `Stacks.SheafOfModules.sheafShrink` brings it down to `SheafOfModules.{w}`. -/

section EssentiallySmall

variable (X : RingedSite.{u, v, w}) [EssentiallySmall.{w} X.C]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F : Stacks.Cohomology.Torsors.AbelianTorsor (unitsAddSheaf X))

attribute [local instance] coefficientSectionRingModule

/-- The coefficient section attached to a section of the torsor is a local generator.

This generalizes `Stacks.Cohomology.Torsors.Generators.coefficientGeneratorSections`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def coefficientGeneratorSections' (U : X.C) (s : F.1.presheaf.obj (op U)) :
    GeneratorSections' X (coefficientSheaf' X F) U := by
  refine ⟨(coefficientSheafEquiv X F U).symm (coefficientGenerator' X F U s), ?_⟩
  intro V f
  have he : (coefficientSheaf' X F).val.restrictₛₗ f.op
        ((coefficientSheafEquiv X F U).symm (coefficientGenerator' X F U s)) =
      (coefficientSheafEquiv X F V).symm
        (coefficientGenerator' X F V (F.1.presheaf.map f.op s)) := by
    apply (coefficientSheafEquiv X F V).injective
    rw [coefficientSheafEquiv_restrict, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      coefficientGenerator_restrict']
    rfl
  rw [he]
  have hfun : (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
        r • (coefficientSheafEquiv X F V).symm
          (coefficientGenerator' X F V (F.1.presheaf.map f.op s))) =
      (coefficientSheafEquiv X F V).symm ∘
        (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
          r • coefficientGenerator' X F V (F.1.presheaf.map f.op s)) := by
    funext r
    apply (coefficientSheafEquiv X F V).injective
    simp only [Function.comp_apply, coefficientSheafEquiv_smul, Equiv.apply_symm_apply]
  rw [hfun]
  exact (coefficientSheafEquiv X F V).symm.bijective.comp
    (coefficientGenerator_bijective' X F V (F.1.presheaf.map f.op s))

/-- The module attached to a torsor under the units is invertible: it is locally free of rank
one, because a section of the torsor trivializes it.

This generalizes `Stacks.Cohomology.Torsors.Generators.coefficientSheaf_isInvertible`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem coefficientSheaf_isInvertible' :
    Stacks.SheafOfModules.IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
      (coefficientSheaf' X F) := by
  apply RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one_of_essentiallySmall
  intro U
  obtain ⟨S, hS, hF⟩ := F.property U
  obtain ⟨I, V, f, rfl⟩ := S.exists_eq_ofArrows
  refine ⟨I, V, f, hS, ?_⟩
  intro i
  obtain ⟨s⟩ := hF (Sieve.ofArrows_mk V f i)
  let e := generatorSectionTrivialization' X (coefficientSheaf' X F) (V i)
    (coefficientGeneratorSections' X F (V i) s)
  exact ⟨(fun _ => e.hom), ⟨cofanFinOneIsColimitOfIso e⟩⟩

/-- The map from a torsor to the generator torsor of its attached module.

This generalizes `Stacks.Cohomology.Torsors.Generators.coefficientGeneratorTorsorHom`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def coefficientGeneratorTorsorHom'
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X) :
    F.val.Hom (generatorTorsor' X hX (coefficientSheaf' X F)
      (coefficientSheaf_isInvertible' X F)).torsor.val where
  hom := {
    app := fun U => ↾(coefficientGeneratorSections' X F U.unop)
    naturality := by
      intro U V f
      ext s
      apply Subtype.ext
      apply (coefficientSheafEquiv X F V.unop).injective
      change coefficientSheafEquiv X F V.unop
          ((coefficientSheafEquiv X F V.unop).symm
            (coefficientGenerator' X F V.unop (F.1.presheaf.map f s))) =
        coefficientSheafEquiv X F V.unop ((coefficientSheaf' X F).val.restrictₛₗ f
          ((coefficientSheafEquiv X F U.unop).symm (coefficientGenerator' X F U.unop s)))
      rw [coefficientSheafEquiv_restrict, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
        coefficientGenerator_restrict']
      rfl }
  map_act := by
    intro U a s
    apply Subtype.ext
    apply (coefficientSheafEquiv X F U.unop).injective
    change coefficientSheafEquiv X F U.unop
        ((coefficientSheafEquiv X F U.unop).symm
          (coefficientGenerator' X F U.unop (F.1.act U a s))) =
      coefficientSheafEquiv X F U.unop
        ((Additive.toMul (Multiplicative.toAdd a) :
              ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U.unop) : Type w)ˣ).val •
          (coefficientSheafEquiv X F U.unop).symm (coefficientGenerator' X F U.unop s))
    rw [coefficientSheafEquiv_smul, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    apply Subtype.ext
    funext V t
    change (torsorUnitBetween' X F (op V.left) t
        (F.1.presheaf.map V.hom.op (F.1.act U a s))).val =
      (X.O.obj.map V.hom.op) (Additive.toMul (Multiplicative.toAdd a)).val *
        (torsorUnitBetween' X F (op V.left) t (F.1.presheaf.map V.hom.op s)).val
    rw [F.1.naturality]
    exact congrArg Units.val (torsorUnitBetween_act_right' X F (op V.left) t
      (F.1.presheaf.map V.hom.op s)
      (Units.map (X.O.obj.map V.hom.op).hom.toMonoidHom
        (Additive.toMul (Multiplicative.toAdd a))))

/-- **Every torsor under the units is a generator torsor.** A torsor is isomorphic to the
generator torsor of the invertible module attached to it.

This generalizes `Stacks.Cohomology.Torsors.Generators.coefficientGeneratorTorsor_isIsomorphic`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem coefficientGeneratorTorsor_isIsomorphic'
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X) :
    Stacks.Cohomology.Torsors.AbelianTorsor.IsIsomorphic F
      (generatorTorsor' X hX (coefficientSheaf' X F) (coefficientSheaf_isInvertible' X F)).torsor :=
  ⟨coefficientGeneratorTorsorHom' X F hX,
    torsorHom_isIso' F.property (coefficientGeneratorTorsorHom' X F hX)⟩

end EssentiallySmall

/-! ### Isomorphisms of modules and of generator torsors -/

/-- The component of an isomorphism of sheaves of modules at an object is bijective. -/
private theorem bijective_app_hom_of_iso
    {X : RingedSite.{u, v, w}}
    {L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (U : X.C) : Function.Bijective (e.hom.val.app (op U)).hom :=
  (ConcreteCategory.isIso_iff_bijective _).mp
    (Functor.map_isIso
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) e.hom)

/-- Multiplication by the image of a section under an isomorphism is bijective exactly when
multiplication by the section is.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorMap_bijective_iff`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem generatorMap_bijective_iff'
    (X : RingedSite.{u, v, w})
    {L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (U : X.C) (s : L.val.obj (op U)) :
    Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) =>
      r • (e.hom.val.app (op U)).hom s) ↔
    Function.Bijective (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) =>
      r • s) := by
  let α := (e.hom.val.app (op U)).hom
  have hα : Function.Bijective α := bijective_app_hom_of_iso e U
  have hfun : (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) => r • α s) =
      α ∘ (fun r => r • s) := by
    funext r
    exact (α.map_smul r s).symm
  rw [hfun]
  exact hα.of_comp_iff' _

/-- A module isomorphism takes a local generator to a local generator.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorSections_mapIso`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorSections_mapIso'
    (X : RingedSite.{u, v, w})
    {L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (U : X.C) (s : GeneratorSections' X L U) : GeneratorSections' X N U := by
  refine ⟨(e.hom.val.app (op U)).hom s.val, ?_⟩
  intro V f
  let α := (e.hom.val.app (op V)).hom
  have hgen := s.property V f
  have hnat := PresheafOfModules.naturality_apply e.hom.val f.op s.val
  have heq : N.val.restrictₛₗ f.op ((e.hom.val.app (op U)).hom s.val) =
      α (L.val.restrictₛₗ f.op s.val) := by
    simpa only [PresheafOfModules.restrictₛₗ_apply] using hnat.symm
  simpa only [heq] using
    (generatorMap_bijective_iff' X e V (L.val.restrictₛₗ f.op s.val)).2 hgen

/-- Transporting a local generator along an isomorphism commutes with restriction.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorSections_mapIso_restrict`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem generatorSections_mapIso_restrict'
    (X : RingedSite.{u, v, w})
    {L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    {U V : X.C} (f : V ⟶ U) (s : GeneratorSections' X L U) :
    generatorSections_mapIso' X e V (generatorSections_restrict' X L f s) =
      generatorSections_restrict' X N f (generatorSections_mapIso' X e U s) := by
  apply Subtype.ext
  simpa [generatorSections_mapIso', generatorSections_restrict',
    PresheafOfModules.restrictₛₗ_apply] using
    PresheafOfModules.naturality_apply e.hom.val f.op s.val

/-- Transporting a local generator along an isomorphism is a bijection.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorSections_mapIso_bijective`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem generatorSections_mapIso_bijective'
    (X : RingedSite.{u, v, w})
    {L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (U : X.C) : Function.Bijective (generatorSections_mapIso' X e U) := by
  constructor
  · intro s t h
    apply Subtype.ext
    exact (bijective_app_hom_of_iso e U).1 (congrArg Subtype.val h)
  · intro t
    refine ⟨generatorSections_mapIso' X e.symm U t, ?_⟩
    apply Subtype.ext
    change (e.hom.val.app (op U)).hom ((e.inv.val.app (op U)).hom t.val) = t.val
    have hcomp' : e.inv.val.app (op U) ≫ e.hom.val.app (op U) = 𝟙 _ := by
      simpa only [SheafOfModules.comp_val, SheafOfModules.id_val,
        PresheafOfModules.comp_app, PresheafOfModules.id_app] using
        congrArg (fun g : N ⟶ N => g.val.app (op U)) e.inv_hom_id
    exact congrArg (fun f => f.hom t.val) hcomp'

/-- The map on sections induced by an isomorphism of modules: transport the corresponding local
generator.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorTorsorMapOfIso`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorTorsorMapOfIso'
    (X : RingedSite.{u, v, w})
    {L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (F : GeneratorTorsor' X L) (G : GeneratorTorsor' X N) (U : X.Cᵒᵖ)
    (s : F.torsor.1.presheaf.obj U) : G.torsor.1.presheaf.obj U :=
  (G.sectionsEquiv U).symm (generatorSections_mapIso' X e U.unop (F.sectionsEquiv U s))

/-- The induced map on sections is compatible with restriction.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorTorsorMapOfIso_restrict`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem generatorTorsorMapOfIso_restrict'
    (X : RingedSite.{u, v, w})
    {L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (F : GeneratorTorsor' X L) (G : GeneratorTorsor' X N) {U V : X.Cᵒᵖ} (f : U ⟶ V)
    (s : F.torsor.1.presheaf.obj U) :
    generatorTorsorMapOfIso' X e F G V (F.torsor.1.presheaf.map f s) =
      G.torsor.1.presheaf.map f (generatorTorsorMapOfIso' X e F G U s) := by
  apply (G.sectionsEquiv V).injective
  apply Subtype.ext
  rw [show (G.sectionsEquiv V) (generatorTorsorMapOfIso' X e F G V
      (F.torsor.1.presheaf.map f s)) =
      generatorSections_mapIso' X e V.unop (F.sectionsEquiv V
        (F.torsor.1.presheaf.map f s)) from
    Equiv.apply_symm_apply _ _]
  rw [G.sectionsEquiv_restrict f (generatorTorsorMapOfIso' X e F G U s),
    show (G.sectionsEquiv U) (generatorTorsorMapOfIso' X e F G U s) =
      generatorSections_mapIso' X e U.unop (F.sectionsEquiv U s) from
      Equiv.apply_symm_apply _ _]
  change (e.hom.val.app V).hom (F.sectionsEquiv V (F.torsor.1.presheaf.map f s)).val =
    N.val.restrictₛₗ f ((e.hom.val.app U).hom (F.sectionsEquiv U s).val)
  rw [F.sectionsEquiv_restrict f s]
  exact PresheafOfModules.naturality_apply e.hom.val f (F.sectionsEquiv U s).val

/-- The induced map on sections is equivariant for the action of the units.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorTorsorMapOfIso_act`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem generatorTorsorMapOfIso_act'
    (X : RingedSite.{u, v, w})
    {L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (F : GeneratorTorsor' X L) (G : GeneratorTorsor' X N) (U : X.Cᵒᵖ)
    (a : (Stacks.Cohomology.Torsors.abelianSheafAsGroupSheaf (unitsAddSheaf X)).presheaf.obj U)
    (s : F.torsor.1.presheaf.obj U) :
    generatorTorsorMapOfIso' X e F G U (F.torsor.1.act U a s) =
      G.torsor.1.act U a (generatorTorsorMapOfIso' X e F G U s) := by
  let : Module (X.O.obj.obj U) (L.val.obj U) := (L.val.obj U).isModule
  let : Module (X.O.obj.obj U) (N.val.obj U) := (N.val.obj U).isModule
  apply (G.sectionsEquiv U).injective
  apply Subtype.ext
  set b : (X.O.obj.obj U)ˣ := Additive.toMul (Multiplicative.toAdd a) with hb
  set x := generatorTorsorMapOfIso' X e F G U s with hx0
  have hF : (F.sectionsEquiv U (F.torsor.1.act U a s)).val =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (L.val.obj U) _ b.val
        (F.sectionsEquiv U s).val := F.sectionsEquiv_smul U b s
  have hG : (G.sectionsEquiv U (G.torsor.1.act U a x)).val =
      @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (N.val.obj U) _ b.val
        (G.sectionsEquiv U x).val := G.sectionsEquiv_smul U b x
  have hx : G.sectionsEquiv U x = generatorSections_mapIso' X e U.unop (F.sectionsEquiv U s) :=
    Equiv.apply_symm_apply _ _
  have hy : G.sectionsEquiv U (generatorTorsorMapOfIso' X e F G U (F.torsor.1.act U a s)) =
      generatorSections_mapIso' X e U.unop (F.sectionsEquiv U (F.torsor.1.act U a s)) :=
    Equiv.apply_symm_apply _ _
  calc (G.sectionsEquiv U (generatorTorsorMapOfIso' X e F G U (F.torsor.1.act U a s))).val
      = (e.hom.val.app U).hom (F.sectionsEquiv U (F.torsor.1.act U a s)).val := by
        rw [hy]
        rfl
    _ = (e.hom.val.app U).hom (@SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U)
          (L.val.obj U) _ b.val (F.sectionsEquiv U s).val) := congrArg _ hF
    _ = @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (N.val.obj U) _ b.val
          ((e.hom.val.app U).hom (F.sectionsEquiv U s).val) :=
        (e.hom.val.app U).hom.map_smul b.val (F.sectionsEquiv U s).val
    _ = @SMul.smul ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (N.val.obj U) _ b.val
          (G.sectionsEquiv U x).val := by
          rw [hx]
          rfl
    _ = (G.sectionsEquiv U (G.torsor.1.act U a x)).val := hG.symm

/-- The morphism of torsors induced by an isomorphism of modules.

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorTorsorHomOfIso`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
def generatorTorsorHomOfIso'
    (X : RingedSite.{u, v, w})
    {L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (F : GeneratorTorsor' X L) (G : GeneratorTorsor' X N) : F.torsor.1.Hom G.torsor.1 where
  hom := {
    app := fun U => ↾(generatorTorsorMapOfIso' X e F G U)
    naturality := by
      intro U V f
      ext s
      exact generatorTorsorMapOfIso_restrict' X e F G f s }
  map_act := generatorTorsorMapOfIso_act' X e F G

/-- **Isomorphic modules have isomorphic generator torsors.**

This generalizes `Stacks.Cohomology.Torsors.Generators.generatorTorsor_isIsomorphic_of_iso`,
stated for `RingedSite.{u, u, u}`, to independent universes. -/
theorem generatorTorsor_isIsomorphic_of_iso'
    (X : RingedSite.{u, v, w})
    {L N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (e : L ≅ N)
    (F : GeneratorTorsor' X L) (G : GeneratorTorsor' X N) :
    Stacks.Cohomology.Torsors.AbelianTorsor.IsIsomorphic F.torsor G.torsor := by
  refine ⟨generatorTorsorHomOfIso' X e F G, ?_⟩
  change IsIso (generatorTorsorHomOfIso' X e F G).hom
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).2
  have h : Function.Bijective (generatorTorsorMapOfIso' X e F G U) :=
    (G.sectionsEquiv U).symm.bijective.comp
      ((generatorSections_mapIso_bijective' X e U.unop).comp (F.sectionsEquiv U).bijective)
  exact h

end Stacks.Cohomology.Torsors.Generators

end
