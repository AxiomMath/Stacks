module

public import StacksFrontier.Deformation.Applications.TwoFibreProductInfRow
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermExact
public import StacksFrontier.Deformation.Applications.TwoFibreProductSixTermFull
public import StacksFrontier.Deformation.Applications.TangentModuleEquivalence
public import StacksFrontier.Deformation.Cofibered.BasedEquivalenceFibre
public import StacksFrontier.Deformation.Artin.Predeformation.FibreProduct
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.ArtinCriteria.RimSchlessinger

/-!
# Comparing 2-fibre products over the big fppf site and over all schemes

Transporting chosen pushforwards along an equivalence; the fact that whether the mediating
`CategoryTheory.TwoFibreProductOver.lift` is an equivalence does not depend on the functors
presenting its legs (`Deformation.isEquivalence_lift_congr`); and the comparison functor
`Deformation.Artin.liftPost` from the 2-fibre product formed over the big fppf site to the one
formed over all schemes over the base, which is an equivalence
(`Deformation.Artin.isEquivalence_liftPost`).
-/

@[expose] public noncomputable section

namespace Deformation

/-! ### Transporting chosen pushforwards along an equivalence -/

section TransportChosenPushforwards
open CategoryTheory CategoryTheory.Functor
universe u₁ v₁ u₂ v₂ u₃ v₃

/-- A choice of pushforwards at a basepoint of a category cofibered in groupoids, built from
the generic existence of pushforwards (`Deformation.exists_pushforward`). -/
public noncomputable def chosenPushforwardsAtOfCofiberedInGroupoids
    {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
    {p : F ⥤ C} (hp : IsCofiberedInGroupoids p) (x : F) :
    ChosenPushforwardsAt p x :=
  ChosenPushforwardsAt.ofCofiberedInGroupoids hp
    (fun A => ⟨pushforwardObj hp A.hom x rfl, pushforwardObj_eq hp A.hom x rfl⟩)
    (fun A => chosenPushforwardMap hp A.hom x rfl)
    (fun A => chosenPushforwardMap_lift hp A.hom x rfl)

/-- `IsHomLift` along a composite functor `a ⋙ r` unfolds to `IsHomLift` for `r` applied to the
image of the arrow under `a`. -/
public theorem isHomLift_comp_iff
    {W : Type u₁} [Category.{v₁} W] {X' : Type u₂} [Category.{v₂} X']
    {C : Type u₃} [Category.{v₃} C] (a : W ⥤ X') (r : X' ⥤ C)
    {R S : C} {u v : W} (k : R ⟶ S) (ψ : u ⟶ v) :
    (a ⋙ r).IsHomLift k ψ ↔ r.IsHomLift k (a.map ψ) := by
  constructor
  · intro h; cases h; exact IsHomLift.map r (a.map ψ)
  · intro h; cases h; exact IsHomLift.map (a ⋙ r) ψ

/-- A strongly cocartesian arrow for `p = a ⋙ r` is carried by an equivalence `a` to a strongly
cocartesian arrow for `r`, over the same base morphism and the image of the arrow. This is the
abstract content of transporting the pushforward structure of `Deformation.ChosenPushforwardsAt`
along the mediating equivalence `CategoryTheory.TwoFibreProductOver.lift` identifies the square
of predeformation categories with. -/
public theorem transport_cocartesian
    {W : Type u₁} [Category.{v₁} W] {X' : Type u₂} [Category.{v₂} X']
    {C : Type u₃} [Category.{v₃} C]
    {p : W ⥤ C} {r : X' ⥤ C} (a : W ⥤ X') (ha : a ⋙ r = p) [a.IsEquivalence]
    {R S : C} {x y : W} (f : R ⟶ S) (φ : x ⟶ y) (hφ : p.IsStronglyCocartesian f φ) :
    r.IsStronglyCocartesian f (a.map φ) := by
  have hpr : ∀ {U V : C} (k : U ⟶ V) {u v : W} (ψ : u ⟶ v),
      p.IsHomLift k ψ ↔ r.IsHomLift k (a.map ψ) := by
    intro U V k u v ψ
    rw [← isHomLift_comp_iff a r k ψ, ha]
  have hlift : r.IsHomLift f (a.map φ) := (hpr f φ).mp hφ.toIsHomLift
  let := hlift
  refine ⟨fun {b''} g'' φ'' hφ'' => ?_⟩
  set b₀ := a.objPreimage b'' with hb₀
  set η : a.obj b₀ ≅ b'' := a.objObjPreimageIso b'' with hη
  have heq : p.obj b₀ = r.obj (a.obj b₀) := (Functor.congr_obj ha b₀).symm
  set ι : p.obj b₀ ≅ r.obj b'' := eqToIso heq ≪≫ r.mapIso η with hι
  set g : S ⟶ p.obj b₀ := g'' ≫ ι.inv with hg
  set φ' : x ⟶ b₀ := a.preimage (φ'' ≫ η.inv) with hφ'
  have hamap : a.map φ' = φ'' ≫ η.inv := a.map_preimage _
  have hιinv : ι.inv = r.map η.inv ≫ eqToHom heq.symm := by simp [hι]
  have hιhom : ι.hom = eqToHom heq ≫ r.map η.hom := by simp [hι]
  have hgg'' : g'' = g ≫ ι.hom := by rw [hg]; simp
  have hplift : p.IsHomLift (f ≫ g) φ' := by
    rw [hpr, hamap, hg, hιinv]
    simp only [← Category.assoc]
    have : r.IsHomLift (f ≫ g'') φ'' := hφ''
    infer_instance
  have := hplift
  obtain ⟨χ', ⟨hχ'lift, hχ'fac⟩, huniq'⟩ := hφ.universal_property' g φ'
  have hχ'lift' : r.IsHomLift g (a.map χ') := (hpr g χ').mp hχ'lift
  set χ'' : a.obj y ⟶ b'' := a.map χ' ≫ η.hom with hχ''def
  have hχ''lift : r.IsHomLift g'' χ'' := by
    rw [hgg'', hιhom, hχ''def]
    simp only [← Category.assoc]
    infer_instance
  have hχ''fac : a.map φ ≫ χ'' = φ'' := by
    rw [hχ''def, ← Category.assoc, ← Functor.map_comp, hχ'fac, hamap]
    simp
  refine ⟨χ'', ⟨hχ''lift, hχ''fac⟩, ?_⟩
  intro ψ'' ⟨hψ''lift, hψ''fac⟩
  set χ₀ : y ⟶ b₀ := a.preimage (ψ'' ≫ η.inv) with hχ₀def
  have hamapχ₀ : a.map χ₀ = ψ'' ≫ η.inv := a.map_preimage _
  have hψ''lift2 : r.IsHomLift g (a.map χ₀) := by
    have : r.IsHomLift g'' ψ'' := hψ''lift
    rw [hamapχ₀, hg, hιinv]
    simp only [← Category.assoc]
    infer_instance
  have hχ₀lift : p.IsHomLift g χ₀ := (hpr g χ₀).mpr hψ''lift2
  have hχ₀fac : φ ≫ χ₀ = φ' := by
    apply a.map_injective
    rw [Functor.map_comp, hamapχ₀, hamap]
    have hh : a.map φ ≫ ψ'' = φ'' := hψ''fac
    rw [← Category.assoc, hh]
  have hχ₀eq : χ₀ = χ' := huniq' χ₀ ⟨hχ₀lift, hχ₀fac⟩
  rw [hχ₀eq] at hamapχ₀
  have hfin : ψ'' = a.map χ' ≫ η.hom := by
    rw [hamapχ₀]
    simp
  rw [hfin, hχ''def]

/-- Swap the witnessed base morphism of a strongly cocartesian arrow from a composite `i ≫ f'`,
with `i` an isomorphism lying over the identity, down to the bare `f'`. -/
public theorem isStronglyCocartesian_of_iso_comp
    {C : Type u₃} [Category.{v₃} C] {X' : Type u₂} [Category.{v₂} X']
    (r : X' ⥤ C) {R R' S : C} {a b : X'} (i : R ⟶ R') [IsIso i] (f' : R' ⟶ S) (φ : a ⟶ b)
    (hi : r.IsHomLift i (𝟙 a)) (hφf : r.IsStronglyCocartesian (i ≫ f') φ)
    (hφ : r.IsHomLift f' φ) :
    r.IsStronglyCocartesian f' φ := by
  have := hi
  have : r.IsStronglyCocartesian i (𝟙 a) := Functor.IsStronglyCocartesian.of_isIso r i (𝟙 a)
  have := hφf
  have : r.IsStronglyCocartesian (i ≫ f') (𝟙 a ≫ φ) := by rw [Category.id_comp]; exact hφf
  have := hφ
  exact Functor.IsStronglyCocartesian.of_comp r (f := i) (g := f') (φ := 𝟙 a) (ψ := φ)

/-- Transport a choice of pushforwards at `w₀` along `p` across an equivalence `a : p ⋙ r = p`
(with `r` the target functor) to a choice of pushforwards at `a.obj w₀` along `r`. This is the
bridge turning a choice of pushforwards for the (older) predeformation-category machinery of
`Deformation.Artin.fibreProductOfPredeformationCategoriesOfEssSurj` into a choice of pushforwards
for `CategoryTheory.TwoFibreProductOver`, along the mediating equivalence Stacks 07WL supplies. -/
public noncomputable def transportChosenPushforwardsAt
    {W : Type u₁} [Category.{v₁} W] {X' : Type u₂} [Category.{v₂} X']
    {C : Type u₃} [Category.{v₃} C]
    {p : W ⥤ C} {r : X' ⥤ C} (a : W ⥤ X') (ha : a ⋙ r = p) [a.IsEquivalence]
    (w₀ : W) (PW : ChosenPushforwardsAt p w₀) :
    ChosenPushforwardsAt r (a.obj w₀) where
  obj A :=
    let heq0 : r.obj (a.obj w₀) = p.obj w₀ := Functor.congr_obj ha w₀
    let i : p.obj w₀ ⟶ r.obj (a.obj w₀) := eqToHom heq0.symm
    let τA : Under (p.obj w₀) := Under.mk (i ≫ A.hom)
    let X := PW.obj τA
    ⟨a.obj X.1, (Functor.congr_obj ha X.1).trans X.2⟩
  inclusion A :=
    let heq0 : r.obj (a.obj w₀) = p.obj w₀ := Functor.congr_obj ha w₀
    let i : p.obj w₀ ⟶ r.obj (a.obj w₀) := eqToHom heq0.symm
    let τA : Under (p.obj w₀) := Under.mk (i ≫ A.hom)
    a.map (PW.inclusion τA)
  inclusion_cocartesian A := by
    set heq0 : r.obj (a.obj w₀) = p.obj w₀ := Functor.congr_obj ha w₀ with hheq0
    set i : p.obj w₀ ⟶ r.obj (a.obj w₀) := eqToHom heq0.symm with hi
    set τA : Under (p.obj w₀) := Under.mk (i ≫ A.hom) with hτA
    set X := PW.obj τA with hX
    set φ : a.obj w₀ ⟶ a.obj X.1 := a.map (PW.inclusion τA) with hφdef
    have hφf : r.IsStronglyCocartesian (i ≫ A.hom) φ :=
      transport_cocartesian a ha (i ≫ A.hom) (PW.inclusion τA) (PW.inclusion_cocartesian τA)
    have hi0 : r.IsHomLift i (𝟙 (a.obj w₀)) := by
      refine IsHomLift.of_fac' r i (𝟙 (a.obj w₀)) heq0 rfl ?_
      simp [hi]
    have hcodA : r.obj (a.obj X.1) = A.right := (Functor.congr_obj ha X.1).trans X.2
    have hfacc : i ≫ A.hom = eqToHom heq0.symm ≫ r.map φ ≫ eqToHom hcodA := by
      have := hφf.toIsHomLift
      exact IsHomLift.fac r (i ≫ A.hom) φ
    have hA' : A.hom = r.map φ ≫ eqToHom hcodA := by
      have hcancel : eqToHom heq0 ≫ i ≫ A.hom =
          eqToHom heq0 ≫ eqToHom heq0.symm ≫ r.map φ ≫ eqToHom hcodA := by
        rw [hfacc]
      simpa [hi] using hcancel
    have hmap : r.map φ = eqToHom (rfl : r.obj (a.obj w₀) = r.obj (a.obj w₀)) ≫
        A.hom ≫ eqToHom hcodA.symm := by
      rw [hA']; simp
    have hφlift : r.IsHomLift A.hom φ :=
      IsHomLift.of_fac' r A.hom φ rfl hcodA hmap
    exact isStronglyCocartesian_of_iso_comp r i A.hom φ hi0 hφf hφlift

end TransportChosenPushforwards

/-! ### Transporting the mediating equivalence along a change of its folded legs -/

section LiftEquivalenceCongr
open CategoryTheory CategoryTheory.Functor
universe u v w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {H : Type u₁} [Category.{v₁} H] {G : Type u₂} [Category.{v₂} G]
  {F : Type u₃} [Category.{v₃} F] {W : Type u₄} [Category.{v₄} W]

/-- Whether `CategoryTheory.TwoFibreProductOver.lift` is an equivalence does not depend on which
(propositionally equal) functor is used to present each leg: a propositional equality `pH = pH'`
(resp. `pG = pG'`) of the two presentations of a leg, together with the corresponding
transported factorizations `hA'`, `hB'`, carries an equivalence proof for the one presentation to
an equivalence proof for the other. This lets an equivalence proved for the presentation used by
`Deformation.Artin.fibreProductOfPredeformationCategoriesOfEssSurj` be reused for the folded
presentation `f ⋙ pF`, `g ⋙ pF` that the "OfLift" lemmas state their hypotheses in terms of. -/
public theorem isEquivalence_lift_congr
    (pF : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (pW : W ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (f : H ⥤ F) (g : G ⥤ F) (A : W ⥤ H) (B : W ⥤ G)
    (pH pH' : H ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (hpH : pH = pH')
    (pG pG' : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k) (hpG : pG = pG')
    (hA : A ⋙ pH = pW) (hA' : A ⋙ pH' = pW)
    (hB : B ⋙ pG = pW) (hB' : B ⋙ pG' = pW)
    (t : A ⋙ f ≅ B ⋙ g)
    (ht : ∀ x, pF.IsHomLift (𝟙 (pW.obj x)) (t.hom.app x))
    (hlift : (TwoFibreProductOver.lift pH pG pF f g pW A B hA hB t ht).IsEquivalence) :
    (TwoFibreProductOver.lift pH' pG' pF f g pW A B hA' hB' t ht).IsEquivalence := by
  subst hpH
  subst hpG
  exact hlift

end LiftEquivalenceCongr

end Deformation

namespace Deformation.Artin

/-! ### Reflecting the slice of the big fppf site out of all schemes over the base -/

section SiteInclusion
open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
universe u uX vX

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The slice of the chosen big fppf site includes into the slice of all schemes over `S`
injectively on objects: an object of `Over S` in the image determines the object of the site it
comes from, because the inclusion of the site is a full-subcategory inclusion. -/
public theorem post_inclusion_obj_injective :
    Function.Injective (Over.post (X := B.obj hS) B.inclusion).obj := by
  intro first second equality
  cases first with
  | mk first terminal arrow =>
    cases second with
    | mk second terminal' arrow' =>
      have hterminal : terminal = terminal' := Subsingleton.elim _ _
      cases hterminal
      have hobject : first = second :=
        ObjectProperty.FullSubcategory.ext (congrArg Over.left equality)
      cases hobject
      have harrows : B.inclusion.map arrow = B.inclusion.map arrow' := by injection equality
      cases B.inclusion.map_injective harrows
      rfl

/-- Being a lift is reflected by the inclusion of the slice of the big fppf site into the slice
of all schemes over `S`: a morphism lying over the image of a morphism of the site already lies
over that morphism. -/
public theorem isHomLift_of_post_inclusion
    {X : Type uX} [Category.{vX} X] (p : X ⥤ AlgebraicGeometry.BigFppfOver B S hS)
    {a b : X} {U V : AlgebraicGeometry.BigFppfOver B S hS}
    (base : U ⟶ V) (arrow : a ⟶ b)
    (hlift : (p ⋙ Over.post B.inclusion).IsHomLift
      ((Over.post B.inclusion).map base) arrow) :
    p.IsHomLift base arrow := by
  have := hlift
  have hdomain := post_inclusion_obj_injective B S hS
    (IsHomLift.domain_eq (p ⋙ Over.post B.inclusion)
      ((Over.post B.inclusion).map base) arrow)
  have hcodomain := post_inclusion_obj_injective B S hS
    (IsHomLift.codomain_eq (p ⋙ Over.post B.inclusion)
      ((Over.post B.inclusion).map base) arrow)
  refine IsHomLift.of_fac' p base arrow hdomain hcodomain ?_
  apply (Over.post B.inclusion).map_injective
  simpa only [Functor.map_comp, Functor.comp_map, eqToHom_map] using
    IsHomLift.fac' (p ⋙ Over.post B.inclusion)
      ((Over.post B.inclusion).map base) arrow

end SiteInclusion

/-! ### The 2-fibre product read in the slice of all schemes over the base -/

section Comparison
open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
universe u u₁ v₁ u₂ v₂ u₃ v₃

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒴 : Type u₂} [Category.{v₂} 𝒴]
  {𝒵 : Type u₃} [Category.{v₃} 𝒵]
variable (p𝒳 : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (p𝒵 : 𝒵 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (Φ : 𝒳 ⥤ 𝒴) (Ψ : 𝒵 ⥤ 𝒴)

attribute [local implicit_reducible] TwoFibreProductOver.lift
  TwoFibreProductOver.structureFunctor TwoFibreProductOver.fst TwoFibreProductOver.snd

/-- The first projection of the 2-fibre product is a `1`-morphism over all schemes over `S`. -/
public theorem fst_comp_post_eq :
    TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ p𝒳 ⋙ Over.post B.inclusion =
      TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion :=
  congrArg (fun H => H ⋙ Over.post B.inclusion) TwoFibreProductOver.fst_comp_eq

/-- The second projection of the 2-fibre product is a `1`-morphism over all schemes over `S`. -/
public theorem snd_comp_post_eq :
    TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ p𝒵 ⋙ Over.post B.inclusion =
      TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion :=
  congrArg (fun H => H ⋙ Over.post B.inclusion) TwoFibreProductOver.snd_comp_eq

/-- The comparison `2`-cell of the 2-fibre product is vertical over all schemes over `S`,
because it is vertical over the site. -/
public theorem isHomLift_psiIso_post (w : TwoFibreProductOver p𝒳 p𝒵 p𝒴 Φ Ψ) :
    (p𝒴 ⋙ Over.post B.inclusion).IsHomLift
      (𝟙 ((TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙
        Over.post B.inclusion).obj w))
      ((TwoFibreProductOver.psiIso p𝒳 p𝒵 p𝒴 Φ Ψ).hom.app w) := by
  have hv := w.vertical
  refine IsHomLift.of_fac' (p𝒴 ⋙ Over.post B.inclusion) _ _
    (congrArg (Over.post B.inclusion).obj
      (@IsHomLift.domain_eq _ _ _ _ p𝒴 _ _ _ _ (𝟙 w.base) w.iso.hom hv))
    (congrArg (Over.post B.inclusion).obj
      (@IsHomLift.codomain_eq _ _ _ _ p𝒴 _ _ _ _ (𝟙 w.base) w.iso.hom hv)) ?_
  show (Over.post B.inclusion).map (p𝒴.map w.iso.hom) = _
  rw [IsHomLift.fac' p𝒴 (𝟙 w.base) w.iso.hom]
  apply Over.OverMorphism.ext
  simp only [Over.post_map, Over.homMk_left, CategoryTheory.Functor.map_comp, Over.comp_left,
    Category.id_comp, Over.eqToHom_left]
  simp only [eqToHom_map, eqToHom_trans]
  rfl

/-- The mediating `1`-morphism comparing the 2-fibre product formed over the site with the
2-fibre product formed over all schemes over `S`. On objects it only replaces the base object
of the site by its underlying scheme over `S`. -/
public abbrev liftPost :
    TwoFibreProductOver p𝒳 p𝒵 p𝒴 Φ Ψ ⥤
      TwoFibreProductOver (p𝒳 ⋙ Over.post B.inclusion) (p𝒵 ⋙ Over.post B.inclusion)
        (p𝒴 ⋙ Over.post B.inclusion) Φ Ψ :=
  TwoFibreProductOver.lift (p𝒳 ⋙ Over.post B.inclusion) (p𝒵 ⋙ Over.post B.inclusion)
    (p𝒴 ⋙ Over.post B.inclusion) Φ Ψ
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙ Over.post B.inclusion)
    (TwoFibreProductOver.fst p𝒳 p𝒵 p𝒴 Φ Ψ) (TwoFibreProductOver.snd p𝒳 p𝒵 p𝒴 Φ Ψ)
    (fst_comp_post_eq B S hS p𝒳 p𝒴 p𝒵 Φ Ψ) (snd_comp_post_eq B S hS p𝒳 p𝒴 p𝒵 Φ Ψ)
    (TwoFibreProductOver.psiIso p𝒳 p𝒵 p𝒴 Φ Ψ) (isHomLift_psiIso_post B S hS p𝒳 p𝒴 p𝒵 Φ Ψ)

/-- Every object of the 2-fibre product formed over all schemes over `S` comes, strictly over
its own base, from an object of the 2-fibre product formed over the site.

The base object of such an object is the image of the base of its `𝒳`-component, hence lies in
the site; its `𝒵`-component lies over the same object of the site because the inclusion is
injective on objects, and its comparison isomorphism is vertical over the site because being a
lift is reflected by the inclusion. -/
public theorem exists_liftPost_iso_over_base
    (U : Over S) (t : TwoFibreProductOver (p𝒳 ⋙ Over.post B.inclusion)
      (p𝒵 ⋙ Over.post B.inclusion) (p𝒴 ⋙ Over.post B.inclusion) Φ Ψ)
    (ht : (TwoFibreProductOver.structureFunctor (p𝒳 ⋙ Over.post B.inclusion)
      (p𝒵 ⋙ Over.post B.inclusion) (p𝒴 ⋙ Over.post B.inclusion) Φ Ψ).obj t = U) :
    ∃ w : TwoFibreProductOver p𝒳 p𝒵 p𝒴 Φ Ψ,
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒵 p𝒴 Φ Ψ ⋙
          Over.post B.inclusion).obj w = U ∧
        ∃ e : (liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ).obj w ≅ t,
          (TwoFibreProductOver.structureFunctor (p𝒳 ⋙ Over.post B.inclusion)
            (p𝒵 ⋙ Over.post B.inclusion) (p𝒴 ⋙ Over.post B.inclusion) Φ Ψ).IsHomLift
            (𝟙 U) e.hom := by
  subst ht
  have hy : p𝒵.obj t.y = p𝒳.obj t.x :=
    post_inclusion_obj_injective B S hS (t.hy.trans t.hx.symm)
  have hvert : p𝒴.IsHomLift (𝟙 (p𝒳.obj t.x)) t.iso.hom := by
    refine isHomLift_of_post_inclusion B S hS p𝒴 (𝟙 (p𝒳.obj t.x)) t.iso.hom ?_
    have h := t.vertical
    have hb : (Over.post B.inclusion).obj (p𝒳.obj t.x) = t.base := t.hx
    rw [(Over.post B.inclusion).map_id, hb]
    exact h
  let w : TwoFibreProductOver p𝒳 p𝒵 p𝒴 Φ Ψ :=
    { base := p𝒳.obj t.x
      x := t.x
      y := t.y
      hx := rfl
      hy := hy
      iso := t.iso
      vertical := hvert }
  have hbase : ((liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ).obj w).base = t.base := t.hx
  have hxw : ((liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ).obj w).x = t.x := rfl
  have hyw : ((liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ).obj w).y = t.y := rfl
  let e₀ : (liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ).obj w ⟶ t :=
    TwoFibreProductOver.Hom.mk' (eqToHom hxw) (eqToHom hyw)
      (by simp only [eqToHom_map, eqToHom_trans])
      (by
        simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp,
          Category.comp_id]
        rfl)
  have ha₀ : IsIso e₀.a := inferInstanceAs (IsIso (eqToHom hxw))
  have hb₀ : IsIso e₀.b := inferInstanceAs (IsIso (eqToHom hyw))
  have : IsIso e₀ :=
    TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ e₀ ha₀ hb₀
  refine ⟨w, t.hx, asIso e₀, ?_⟩
  refine IsHomLift.of_fac' _ _ _ hbase rfl ?_
  show e₀.hbase = _
  rw [show e₀.hbase = TwoFibreProductOver.Hom.hbase
    (TwoFibreProductOver.Hom.mk' (eqToHom hxw) (eqToHom hyw) _ _) from rfl,
    TwoFibreProductOver.Hom.mk'_hbase]
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- The comparison `1`-morphism is faithful: a morphism of a 2-fibre product is determined by
its two components, and the comparison leaves both unchanged. -/
public theorem faithful_liftPost : (liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ).Faithful := by
  constructor
  intro w w' φ φ' h
  exact TwoFibreProductOver.Hom.ext' (congrArg (fun m => m.a) h) (congrArg (fun m => m.b) h)

/-- The comparison `1`-morphism is full: the two components of a morphism of the 2-fibre product
formed over all schemes over `S` are already a morphism of the 2-fibre product formed over the
site, because they induce one and the same morphism of the site — the inclusion being faithful
is what turns the equality of the two induced morphisms of `Over S` into the equality over the
site. -/
public theorem full_liftPost : (liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ).Full := by
  constructor
  intro w w' θ
  have hbase : eqToHom w.hy.symm ≫ p𝒵.map θ.b ≫ eqToHom w'.hy =
      eqToHom w.hx.symm ≫ p𝒳.map θ.a ≫ eqToHom w'.hx := by
    have hb := θ.hb
    have ha := θ.ha
    apply (Over.post B.inclusion).map_injective
    simp only [CategoryTheory.Functor.map_comp, eqToHom_map]
    exact (IsHomLift.fac (p𝒵 ⋙ Over.post B.inclusion) θ.hbase θ.b).symm.trans
      (IsHomLift.fac (p𝒳 ⋙ Over.post B.inclusion) θ.hbase θ.a)
  exact ⟨TwoFibreProductOver.Hom.mk' θ.a θ.b hbase θ.w,
    TwoFibreProductOver.Hom.ext' rfl rfl⟩

/-- The comparison `1`-morphism is essentially surjective. -/
public theorem essSurj_liftPost : (liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ).EssSurj := by
  constructor
  intro t
  obtain ⟨w, -, e, -⟩ := exists_liftPost_iso_over_base B S hS p𝒳 p𝒴 p𝒵 Φ Ψ _ t rfl
  exact ⟨w, ⟨e⟩⟩

/-- The 2-fibre product formed over the chosen big fppf site agrees with the 2-fibre product
formed over all schemes over `S`: the comparison `1`-morphism is an equivalence. -/
public theorem isEquivalence_liftPost : (liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ).IsEquivalence := by
  have := faithful_liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ
  have := full_liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ
  have := essSurj_liftPost B S hS p𝒳 p𝒴 p𝒵 Φ Ψ
  exact {}

end Comparison

end Deformation.Artin

end
