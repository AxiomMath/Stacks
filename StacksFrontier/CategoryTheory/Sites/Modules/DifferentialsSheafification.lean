module

public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.Differentials
public import StacksFrontier.CategoryTheory.Sites.Modules.PrincipalPartsSheafification
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of relative differentials of a sheafification

Let `f : O₁ ⟶ O₂` be a morphism of presheaves of commutative rings on a site. Stacks Tag 08TP
asserts that the sheaf of relative differentials `Ω_{O₂^#/O₁^#}` of the associated sheaves of
rings is the sheaf associated to the presheaf `X ↦ Ω[O₂(X)⁄O₁(X)]` of objectwise modules of
Kähler differentials. This file proves that, together with the equation that pins the
comparison down: the inverse of the comparison carries the image of the objectwise universal
differential `d b` to the sheaf-level universal derivation evaluated on the image of `b`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.additiveLift`: a presheaf of commutative rings, as a
  presheaf of abelian groups whose sections are lifted to a larger universe, with
  `additiveLiftMap` its functoriality and `additiveUp`, `additiveDown` the passage between a
  section of `A` and a section of `additiveLift A`.
* `AlgebraicGeometry.SheafOfModules.objectwiseRelativeDifferentials`: the presheaf of
  modules `X ↦ Ω[O₂(X)⁄O₁(X)]`, with its values lifted to the coefficient-module universe.
* `AlgebraicGeometry.SheafOfModules.sheafifiedObjectwiseDifferentials`: its associated sheaf
  of modules, formed along the ring-valued sheafification map of `O₂`, with
  `sheafifiedUniversalDerivation` the relative derivation of `O₂^#` over `O₁^#` that it
  carries and `objectwiseDifferentialInSheafification` the image in it of an objectwise
  universal differential.
* `AlgebraicGeometry.SheafOfModules.corepresentableByIso`: the isomorphism between two
  corepresenting objects of one functor, with the inverse spelled as the morphism attached to
  the universal element of the source.

## Main results

* `AlgebraicGeometry.SheafOfModules.derivation_ext_of_isLocallySurjective`: two relative
  derivations with values in a sheaf agreeing on the image of a locally surjective map of
  presheaves of commutative rings are equal.
* `AlgebraicGeometry.SheafOfModules.existsUnique_derivation_extension`: along a locally
  bijective morphism `α : A ⟶ B` of presheaves of commutative rings, a family of additive
  maps out of `A` with values in a *sheaf* of `B`-modules, which is `α`-semilinearly Leibniz,
  compatible with restriction and kills `A₁`, extends uniquely to a relative derivation of
  `B` over `B₁`.
* `AlgebraicGeometry.SheafOfModules.existsUnique_desc_sheafifiedObjectwiseDifferentials`: every
  relative derivation of `O₂^#` over `O₁^#` with values in a sheaf of modules factors uniquely
  through `sheafifiedUniversalDerivation`.
* `AlgebraicGeometry.SheafOfModules.differentialsSheafificationIso` and
  `AlgebraicGeometry.SheafOfModules.differentialsSheafificationIso_inv_unit_d`: Tag 08TP, the
  comparison isomorphism and the equation that determines it.

## Implementation notes

The comparison is obtained from universal properties rather than from the presentations of
Tag 04BM: both sides corepresent the functor of relative derivations of `O₂^#` over `O₁^#`,
and `Functor.coreprX` is the object of Tag 04BL, so the isomorphism is `corepresentableByIso`
applied to the two corepresentations. The coefficient sheaves of modules live in
`SheafOfModules.{max u u₁ v₁ v}`, the universe in which the corepresentability of Tag 04BL is
available; `u`, `u₁`, `v₁` and `v` are free and the site is not assumed small.

## References

* [Stacks Project, Tag 08TP](https://stacks.math.columbia.edu/tag/08TP)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), corepresentability
  of the functor of relative derivations.
-/

@[expose] public section

open CategoryTheory Opposite

universe w₀ t v v₁ u u₁

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

/-- The additive group underlying a commutative ring, with its carrier lifted to a larger
universe. -/
noncomputable abbrev additiveForget : CommRingCat.{u} ⥤ AddCommGrpCat.{max u w₀} :=
  forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u} ⋙
    AddCommGrpCat.uliftFunctor.{w₀, u}

/-- A presheaf of commutative rings, regarded as a presheaf of abelian groups whose sections
are lifted to a larger universe. -/
noncomputable abbrev additiveLift (A : Cᵒᵖ ⥤ CommRingCat.{u}) :
    Cᵒᵖ ⥤ AddCommGrpCat.{max u w₀} :=
  A ⋙ additiveForget.{w₀}

/-- A morphism of presheaves of commutative rings, as a morphism of the associated
universe-lifted presheaves of abelian groups. -/
noncomputable abbrev additiveLiftMap {A B : Cᵒᵖ ⥤ CommRingCat.{u}} (α : A ⟶ B) :
    additiveLift.{w₀} A ⟶ additiveLift.{w₀} B :=
  Functor.whiskerRight α additiveForget.{w₀}

/-- A section of `A` over `X`, as a section of `additiveLift A`. -/
def additiveUp {A : Cᵒᵖ ⥤ CommRingCat.{u}} {X : Cᵒᵖ} (x : A.obj X) :
    ToType ((additiveLift.{w₀} A).obj X) := ULift.up x

/-- The section of `A` underlying a section of `additiveLift A`. -/
def additiveDown {A : Cᵒᵖ ⥤ CommRingCat.{u}} {X : Cᵒᵖ}
    (x : ToType ((additiveLift.{w₀} A).obj X)) : A.obj X := ULift.down x

/-- The sieve on which two sections of `additiveLift A` agree is the sieve on which the two
underlying sections of `A` agree. -/
lemma additiveLift_equalizerSieve {A : Cᵒᵖ ⥤ CommRingCat.{u}} {X : Cᵒᵖ}
    (x y : ToType ((additiveLift.{w₀} A).obj X)) :
    Presheaf.equalizerSieve x y
      = Presheaf.equalizerSieve (F := A) (additiveDown x) (additiveDown y) := by
  ext Y g
  exact ⟨fun h ↦ congrArg additiveDown h, fun h ↦ congrArg additiveUp h⟩

/-- The sieve on which a section of `additiveLift B` is in the image of `additiveLiftMap α`
is the sieve on which the underlying section of `B` is in the image of `α`. -/
lemma additiveLift_imageSieve {A B : Cᵒᵖ ⥤ CommRingCat.{u}} (α : A ⟶ B) {X : C}
    (s : ToType ((additiveLift.{w₀} B).obj (op X))) :
    Presheaf.imageSieve (additiveLiftMap.{w₀} α) s
      = Presheaf.imageSieve α (additiveDown s) := by
  ext Y g
  exact ⟨fun ⟨c, hc⟩ ↦ ⟨additiveDown c, congrArg additiveDown hc⟩,
    fun ⟨c, hc⟩ ↦ ⟨additiveUp c, congrArg additiveUp hc⟩⟩

/-- Local injectivity passes to the universe-lifted presheaves of abelian groups. -/
lemma additiveLiftMap_isLocallyInjective {A B : Cᵒᵖ ⥤ CommRingCat.{u}} (α : A ⟶ B)
    [Presheaf.IsLocallyInjective J α] :
    Presheaf.IsLocallyInjective J (additiveLiftMap.{w₀} α) where
  equalizerSieve_mem x y h := by
    rw [additiveLift_equalizerSieve]
    exact Presheaf.equalizerSieve_mem J α _ _ (congrArg additiveDown h)

/-- Local surjectivity passes to the universe-lifted presheaves of abelian groups. -/
lemma additiveLiftMap_isLocallySurjective {A B : Cᵒᵖ ⥤ CommRingCat.{u}} (α : A ⟶ B)
    [Presheaf.IsLocallySurjective J α] :
    Presheaf.IsLocallySurjective J (additiveLiftMap.{w₀} α) where
  imageSieve_mem s := by
    rw [additiveLift_imageSieve]
    exact Presheaf.imageSieve_mem J α _

/-- Sections of a sheaf of modules agreeing after restriction to a covering sieve are equal. -/
private lemma eq_of_restrict_eq {B : Cᵒᵖ ⥤ CommRingCat.{u}}
    {M : PresheafOfModules.{t} (B ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (hM : Presheaf.IsSheaf J M.presheaf) {X : Cᵒᵖ} (S : Sieve X.unop) (hS : S ∈ J X.unop)
    (x y : M.obj X) (h : ∀ (Y : C) (g : Y ⟶ X.unop), S g → M.map g.op x = M.map g.op y) :
    x = y :=
  hM.isSeparated _ S hS x y h

/-- **Two relative derivations agreeing on the image of a locally surjective map of
presheaves of commutative rings are equal**, provided the coefficient presheaf of modules is
a sheaf. -/
theorem derivation_ext_of_isLocallySurjective
    {A B : Cᵒᵖ ⥤ CommRingCat.{u}} (α : A ⟶ B) [Presheaf.IsLocallySurjective J α]
    {B₁ : Cᵒᵖ ⥤ CommRingCat.{u}} {φ₂ : B₁ ⟶ B}
    {M : PresheafOfModules.{t} (B ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (hM : Presheaf.IsSheaf J M.presheaf) (D D' : PresheafOfModulesOfCommRing.Derivation' M φ₂)
    (h : ∀ (X : Cᵒᵖ) (b : A.obj X), D.d (α.app X b) = D'.d (α.app X b)) : D = D' := by
  ext X b
  refine eq_of_restrict_eq J hM _ (Presheaf.imageSieve_mem J α b) _ _ ?_
  rintro Y g ⟨c, hc⟩
  rw [← D.d_map, ← D'.d_map, ← hc, h]

/-- **Extension of a relative derivation along a locally bijective map of presheaves of
commutative rings.** Let `α : A ⟶ B` be locally bijective, let `α₁ : A₁ ⟶ B₁` be locally
surjective, and let `φ₁ : A₁ ⟶ A` and `φ₂ : B₁ ⟶ B` satisfy `α ∘ φ₁ = φ₂ ∘ α₁`. Let `M` be a
presheaf of `B`-modules whose underlying presheaf of abelian groups is a sheaf. Then a family
of additive maps `d₀ : A(X) →+ M(X)`, satisfying the Leibniz rule `α`-semilinearly, compatible
with restriction, and vanishing on the image of `φ₁`, extends to a relative derivation of `B`
over `B₁` with values in `M`, and does so in exactly one way. -/
theorem existsUnique_derivation_extension
    {A B : Cᵒᵖ ⥤ CommRingCat.{u}} (α : A ⟶ B)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [HasWeakSheafify J AddCommGrpCat.{max u w₀}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u w₀}]
    {A₁ B₁ : Cᵒᵖ ⥤ CommRingCat.{u}} (φ₁ : A₁ ⟶ A) (φ₂ : B₁ ⟶ B) (α₁ : A₁ ⟶ B₁)
    [Presheaf.IsLocallySurjective J α₁]
    (hsq : ∀ (X : Cᵒᵖ) (s : A₁.obj X), α.app X (φ₁.app X s) = φ₂.app X (α₁.app X s))
    {M : PresheafOfModules.{max u w₀} (B ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (hM : Presheaf.IsSheaf J M.presheaf)
    (d₀ : ∀ {X : Cᵒᵖ}, A.obj X →+ M.obj X)
    (d₀_mul : ∀ {X : Cᵒᵖ} (x y : A.obj X),
      d₀ (x * y) = α.app X x • d₀ y + α.app X y • d₀ x)
    (d₀_map : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : A.obj X), d₀ (A.map g x) = M.map g (d₀ x))
    (d₀_app : ∀ {X : Cᵒᵖ} (s : A₁.obj X), d₀ (φ₁.app X s) = 0) :
    ∃! D : PresheafOfModulesOfCommRing.Derivation' M φ₂,
      ∀ (X : Cᵒᵖ) (b : A.obj X), D.d (α.app X b) = d₀ b := by
  classical
  let : Presheaf.IsLocallyInjective J (additiveLiftMap.{w₀} α) :=
    additiveLiftMap_isLocallyInjective J α
  let : Presheaf.IsLocallySurjective J (additiveLiftMap.{w₀} α) :=
    additiveLiftMap_isLocallySurjective J α
  let d₀' : additiveLift.{w₀} A ⟶ M.presheaf :=
    { app := fun X ↦ AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (fun x ↦ d₀ (additiveDown x))
          (fun x y ↦ d₀.map_add (additiveDown x) (additiveDown y)))
      naturality := fun X Y g ↦ by
        ext x
        exact d₀_map g (additiveDown x) }
  obtain ⟨d₁, hd₁⟩ :=
    ((J.W_of_isLocallyBijective (additiveLiftMap.{w₀} α)) M.presheaf hM).2 d₀'
  let dd : ∀ (X : Cᵒᵖ), B.obj X → M.obj X := fun X b ↦ (d₁.app X) (additiveUp b)
  have hadd : ∀ (X : Cᵒᵖ) (b b' : B.obj X), dd X (b + b') = dd X b + dd X b' :=
    fun X b b' ↦ (d₁.app X).hom.map_add (additiveUp b) (additiveUp b')
  have key : ∀ (X : Cᵒᵖ) (x : A.obj X), dd X ((α.app X) x) = d₀ x := fun X x ↦
    congrArg (fun z : additiveLift.{w₀} A ⟶ M.presheaf ↦ z.app X (additiveUp x)) hd₁
  have hnat : ∀ {X Y : Cᵒᵖ} (g : X ⟶ Y) (b : B.obj X),
      dd Y ((B.map g) b) = M.map g (dd X b) :=
    fun g b ↦ NatTrans.naturality_apply d₁ g (additiveUp b)
  refine ⟨{ d := fun {X} ↦ AddMonoidHom.mk' (dd X) (hadd X)
            d_mul := ?_
            d_map := fun g x ↦ hnat g x
            d_app := ?_ }, key, fun D hD ↦
    derivation_ext_of_isLocallySurjective J α hM D _ fun X b ↦ (hD X b).trans (key X b).symm⟩
  · intro X b b'
    show dd X (b * b') = b • dd X b' + b' • dd X b
    refine eq_of_restrict_eq J hM _
      (J.intersection_covering (Presheaf.imageSieve_mem J α b)
        (Presheaf.imageSieve_mem J α b')) _ _ ?_
    rintro Y g ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩
    have hs : ((B ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map g.op) b = α.app (op Y) c :=
      hc.symm
    have hs' : ((B ⋙ forget₂ CommRingCat.{u} RingCat.{u}).map g.op) b' = α.app (op Y) c' :=
      hc'.symm
    rw [map_add, M.map_smul, M.map_smul, ← hnat, ← hnat, ← hnat, map_mul, ← hc, ← hc',
      ← map_mul, key, key, key, d₀_mul, hs, hs']
    rfl
  · intro X s
    show dd X ((φ₂.app X) s) = 0
    refine eq_of_restrict_eq J hM _ (Presheaf.imageSieve_mem J α₁ s) _ _ ?_
    rintro Y g ⟨c, hc⟩
    have h0 : dd (op Y) ((B.map g.op) ((φ₂.app X) s)) = 0 := by
      rw [← NatTrans.naturality_apply φ₂ g.op s, ← hc, ← hsq, key, d₀_app]
    rw [← hnat, h0, map_zero]
    rfl

/-- Two corepresentations of one functor give an isomorphism of the corepresenting objects,
whose inverse is the morphism corresponding to the universal element of the source. -/
@[simps]
def corepresentableByIso {D : Type u₁} [Category.{v₁} D] {F : D ⥤ Type t} {X X' : D}
    (e : F.CorepresentableBy X) (e' : F.CorepresentableBy X') : X ≅ X' where
  hom := e.homEquiv.symm (e'.homEquiv (𝟙 X'))
  inv := e'.homEquiv.symm (e.homEquiv (𝟙 X))
  hom_inv_id := by
    apply e.homEquiv.injective
    rw [e.homEquiv_comp, Equiv.apply_symm_apply, ← e'.homEquiv_comp, Category.id_comp,
      Equiv.apply_symm_apply]
  inv_hom_id := by
    apply e'.homEquiv.injective
    rw [e'.homEquiv_comp, Equiv.apply_symm_apply, ← e.homEquiv_comp, Category.id_comp,
      Equiv.apply_symm_apply]

section Sheafification

open Stacks.SheafOfModules

variable [HasWeakSheafify J CommRingCat.{u}] [J.WEqualsLocallyBijective CommRingCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{max u u₁ v₁ v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u u₁ v₁ v}]
  {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The objectwise presheaf of relative Kähler differentials of a morphism of presheaves of
commutative rings, with its values lifted to the universe of the coefficient sheaves. -/
noncomputable abbrev objectwiseRelativeDifferentials (f : O₁ ⟶ O₂) :
    PresheafOfModules.{max u u₁ v₁ v} (O₂ ⋙ forget₂ CommRingCat.{u} RingCat.{u}) :=
  liftPresheaf.{v, v₁, u, u₁}
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' f)

/-- The sheaf of modules associated to the objectwise relative differentials, formed along the
ring-valued sheafification map of `O₂`. -/
noncomputable abbrev sheafifiedObjectwiseDifferentials (f : O₁ ⟶ O₂) :
    _root_.SheafOfModules.{max u u₁ v₁ v}
      (Stacks.SheafOfModules.Tensor.ringSheaf (associatedCommRingSheaf J O₂)) :=
  (PresheafOfModules.sheafification (toAssociatedRingSheaf J O₂)).obj
    (objectwiseRelativeDifferentials.{v, v₁} f)

/-- The image of the objectwise universal differential `d b` in the associated sheaf of
modules. -/
noncomputable def objectwiseDifferentialInSheafification (f : O₁ ⟶ O₂) (X : Cᵒᵖ)
    (b : O₂.obj X) : (sheafifiedObjectwiseDifferentials.{v, v₁} J f).val.obj X :=
  ((PresheafOfModules.sheafificationAdjunction (toAssociatedRingSheaf J O₂)).unit.app
      (objectwiseRelativeDifferentials.{v, v₁} f)).app X
    ((liftedDiffDerivation.{v₁, u, u₁, v} f).d b)

/-- **The universal derivation on the sheafification of the objectwise differentials.**
There is exactly one relative derivation of `O₂^#` over `O₁^#` with values in the sheaf
associated to the objectwise differentials that sends the image of a section `b` of `O₂` to
the image of the objectwise universal differential `d b`. -/
theorem existsUnique_derivation_sheafifiedObjectwiseDifferentials (f : O₁ ⟶ O₂) :
    ∃! D : PresheafOfModulesOfCommRing.Derivation'
        (sheafifiedObjectwiseDifferentials.{v, v₁} J f).val (associatedCommRingSheafMap J f).hom,
      ∀ (X : Cᵒᵖ) (b : O₂.obj X), D.d ((toSheafify J O₂).app X b)
        = objectwiseDifferentialInSheafification.{v, v₁} J f X b := by
  let η := (PresheafOfModules.sheafificationAdjunction (toAssociatedRingSheaf J O₂)).unit.app
    (objectwiseRelativeDifferentials.{v, v₁} f)
  let D₀ := (liftedDiffDerivation.{v₁, u, u₁, v} f).postcomp η
  exact existsUnique_derivation_extension.{max u₁ v₁ v} J (toSheafify J O₂) f
    (associatedCommRingSheafMap J f).hom (toSheafify J O₁)
    (fun X s ↦ congrArg (fun r : O₁ ⟶ sheafify J O₂ ↦ r.app X s) (toSheafify_naturality J f))
    (M := (sheafifiedObjectwiseDifferentials.{v, v₁} J f).val)
    (sheafifiedObjectwiseDifferentials.{v, v₁} J f).isSheaf
    (fun {X} ↦ D₀.d) (fun x y ↦ D₀.d_mul x y) (fun g x ↦ D₀.d_map g x) (fun s ↦ D₀.d_app s)

/-- The universal relative derivation on the sheaf associated to the objectwise
differentials. -/
noncomputable def sheafifiedUniversalDerivation (f : O₁ ⟶ O₂) :
    PresheafOfModulesOfCommRing.Derivation' (sheafifiedObjectwiseDifferentials.{v, v₁} J f).val
      (associatedCommRingSheafMap J f).hom :=
  (existsUnique_derivation_sheafifiedObjectwiseDifferentials.{v, v₁} J f).choose

/-- `sheafifiedUniversalDerivation` sends the image of a section `b` of `O₂` to the image of
the objectwise universal differential `d b`. -/
lemma sheafifiedUniversalDerivation_d (f : O₁ ⟶ O₂) (X : Cᵒᵖ) (b : O₂.obj X) :
    (sheafifiedUniversalDerivation.{v, v₁} J f).d ((toSheafify J O₂).app X b)
      = objectwiseDifferentialInSheafification.{v, v₁} J f X b :=
  (existsUnique_derivation_sheafifiedObjectwiseDifferentials.{v, v₁} J f).choose_spec.1 X b

/-- The restriction along the sheafification maps of a relative derivation of the associated
sheaves of rings. -/
noncomputable def restrictDerivationAlongSheafification (f : O₁ ⟶ O₂)
    {F : PresheafOfModules.{max u u₁ v₁ v}
      (Stacks.SheafOfModules.Tensor.ringSheaf (associatedCommRingSheaf J O₂)).obj}
    (D : PresheafOfModulesOfCommRing.Derivation' F (associatedCommRingSheafMap J f).hom) :
    PresheafOfModulesOfCommRing.Derivation' 
      ((PresheafOfModules.restrictScalars (toAssociatedRingSheaf J O₂)).obj F) f where
  d {X} := AddMonoidHom.mk' (fun b ↦ D.d ((toSheafify J O₂).app X b))
    (fun b b' ↦ (congrArg D.d (map_add ((toSheafify J O₂).app X).hom b b')).trans
      (map_add D.d _ _))
  d_mul x y :=
    (congrArg D.d (map_mul ((toSheafify J O₂).app _).hom x y)).trans (D.d_mul _ _)
  d_map g x :=
    (congrArg D.d (NatTrans.naturality_apply (toSheafify J O₂) g x)).trans (D.d_map g _)
  d_app s :=
    (congrArg D.d (congrArg (fun r : O₁ ⟶ sheafify J O₂ ↦ r.app _ s)
      (toSheafify_naturality J f))).trans (D.d_app _)

/-- **The universal property of the sheafified objectwise differentials.** Every relative
derivation of `O₂^#` over `O₁^#` with values in a sheaf of modules factors uniquely through
`sheafifiedUniversalDerivation`. -/
theorem existsUnique_desc_sheafifiedObjectwiseDifferentials (f : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules.{max u u₁ v₁ v}
      (Stacks.SheafOfModules.Tensor.ringSheaf (associatedCommRingSheaf J O₂)))
    (D : PresheafOfModulesOfCommRing.Derivation' F.val (associatedCommRingSheafMap J f).hom) :
    ∃! g : sheafifiedObjectwiseDifferentials.{v, v₁} J f ⟶ F,
      (sheafifiedUniversalDerivation.{v, v₁} J f).postcomp g.val = D := by
  classical
  let dQ := liftedDiffDerivation.{v₁, u, u₁, v} f
  let eQ := liftedDiffUniversal.{v, v₁, u, u₁} f
  let D' := restrictDerivationAlongSheafification.{v, v₁} J f D
  let g₀ := eQ.desc D'
  let g := (PresheafOfModules.sheafificationHomEquiv (toAssociatedRingSheaf J O₂)).symm g₀
  have hfac : ∀ (X : Cᵒᵖ) (b : O₂.obj X),
      g₀.app X (dQ.d b) = D.d ((toSheafify J O₂).app X b) :=
    fun X b ↦ congrArg (fun E : _ ↦ E.d b) (eQ.fac D')
  have hunit : ∀ (h : sheafifiedObjectwiseDifferentials.{v, v₁} J f ⟶ F) (X : Cᵒᵖ)
      (b : O₂.obj X),
      (PresheafOfModules.sheafificationHomEquiv (toAssociatedRingSheaf J O₂) h).app X
          (dQ.d b)
        = h.val.app X (objectwiseDifferentialInSheafification.{v, v₁} J f X b) :=
    fun h X b ↦ rfl
  have hgg : (PresheafOfModules.sheafificationHomEquiv (toAssociatedRingSheaf J O₂)) g = g₀ :=
    (PresheafOfModules.sheafificationHomEquiv (toAssociatedRingSheaf J O₂)).apply_symm_apply g₀
  have hg : ∀ (X : Cᵒᵖ) (b : O₂.obj X),
      g.val.app X (objectwiseDifferentialInSheafification.{v, v₁} J f X b)
        = D.d ((toSheafify J O₂).app X b) := fun X b ↦ by
    rw [← hunit g X b, hgg]
    exact hfac X b
  refine ⟨g, ?_, ?_⟩
  · refine derivation_ext_of_isLocallySurjective J (toSheafify J O₂) F.isSheaf _ _ ?_
    intro X b
    show g.val.app X ((sheafifiedUniversalDerivation.{v, v₁} J f).d
      ((toSheafify J O₂).app X b)) = _
    rw [sheafifiedUniversalDerivation_d, hg]
  · intro h hh
    apply (PresheafOfModules.sheafificationHomEquiv (toAssociatedRingSheaf J O₂)).injective
    rw [hgg]
    refine eQ.postcomp_injective _ _ ?_
    ext X b
    show (PresheafOfModules.sheafificationHomEquiv (toAssociatedRingSheaf J O₂) h).app X
      (dQ.d b) = g₀.app X (dQ.d b)
    rw [hunit h X b, hfac X b, ← sheafifiedUniversalDerivation_d.{v, v₁} J f X b]
    exact congrArg (fun E : PresheafOfModulesOfCommRing.Derivation' F.val _ ↦
      E.d ((toSheafify J O₂).app X b)) hh

/-- The sheaf associated to the objectwise relative differentials corepresents the functor of
relative derivations of the associated sheaves of commutative rings. -/
noncomputable def sheafifiedObjectwiseDifferentialsCorepresentableBy (f : O₁ ⟶ O₂) :
    (derivationsFunctor.{v} (associatedCommRingSheaf J O₁) (associatedCommRingSheaf J O₂)
        (associatedCommRingSheafMap J f)).CorepresentableBy
      (sheafifiedObjectwiseDifferentials.{v, v₁} J f) :=
  universalDerivationCorepresentableBy.{v, v₁, u, u₁} _ _ _
    (sheafifiedUniversalDerivation.{v, v₁} J f)
    (existsUnique_desc_sheafifiedObjectwiseDifferentials.{v, v₁} J f)

/-- **Stacks Project, Tag 08TP.** Relative differentials commute with passing from presheaves
of commutative rings to their associated sheaves: the sheaf of differentials of `O₂^#` over
`O₁^#` is canonically the sheaf associated to the presheaf `X ↦ Ω[O₂(X)⁄O₁(X)]`. -/
@[stacks 08TP "isomorphism"]
noncomputable def differentialsSheafificationIso (O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{u})
    (f : O₁ ⟶ O₂) :
    (derivationsFunctor.{v} (associatedCommRingSheaf J O₁) (associatedCommRingSheaf J O₂)
        (associatedCommRingSheafMap J f)).coreprX ≅
      sheafifiedObjectwiseDifferentials.{v, v₁} J f :=
  corepresentableByIso (derivationsFunctor.{v} (associatedCommRingSheaf J O₁)
      (associatedCommRingSheaf J O₂) (associatedCommRingSheafMap J f)).corepresentableBy
    (sheafifiedObjectwiseDifferentialsCorepresentableBy.{v, v₁} J f)

/-- **Stacks Project, Tag 08TP**, the canonicality of the comparison: the inverse of
`differentialsSheafificationIso` carries the image of the objectwise universal differential
`d b` to the sheaf-level universal derivation evaluated on the image of `b`. -/
@[stacks 08TP "canonicality"]
lemma differentialsSheafificationIso_inv_unit_d (O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{u})
    (f : O₁ ⟶ O₂) (X : Cᵒᵖ) (b : O₂.obj X) :
    ((differentialsSheafificationIso.{v, v₁} J O₁ O₂ f).inv.val.app X)
        (objectwiseDifferentialInSheafification.{v, v₁} J f X b) =
      (derivationsFunctor.{v} (associatedCommRingSheaf J O₁) (associatedCommRingSheaf J O₂)
        (associatedCommRingSheafMap J f)).coreprx.d
          ((toAssociatedRingSheaf J O₂).app X b) := by
  let G := derivationsFunctor.{v} (associatedCommRingSheaf J O₁)
    (associatedCommRingSheaf J O₂) (associatedCommRingSheafMap J f)
  have h1 := (sheafifiedObjectwiseDifferentialsCorepresentableBy.{v, v₁} J f).homEquiv
    |>.apply_symm_apply (G.corepresentableBy.homEquiv (𝟙 G.coreprX))
  rw [← sheafifiedUniversalDerivation_d.{v, v₁} J f X b]
  exact congrArg (fun E : PresheafOfModulesOfCommRing.Derivation' G.coreprX.val
      (associatedCommRingSheafMap J f).hom ↦
    E.d ((toSheafify J O₂).app X b)) h1

end Sheafification

end AlgebraicGeometry.SheafOfModules
