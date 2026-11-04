module

public import StacksFrontier.CategoryTheory.FiberedCategory.GrothendieckArrowCancellation
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackAdjunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Attaching a morphism of a Grothendieck construction to a strongly cartesian morphism

Let `F` be a pseudofunctor from the locally discrete bicategory on `𝒞ᵒᵖ` to `Cat`, so that the
Grothendieck construction `∫ᶜ F` is a fibred category over `𝒞`, and let `N : ∫ᶜ F ⥤ 𝒯` be a
1-morphism of fibred categories over `r : 𝒯 ⥤ 𝒞`.

`StacksFrontier.CategoryTheory.FiberedCategory.GrothendieckArrowCancellation` reads a morphism of
`𝒯` out of an object which is isomorphic *over an identity* to the image of an object of a fibre
in the normal form `CategoryTheory.Pseudofunctor.CoGrothendieck.homOf`. This file supplies the two
things that are needed to put a morphism of `𝒯` into that situation and to compare two such
readings: a strongly cartesian morphism into the image of an object of a fibre produces the
required isomorphism over an identity, and for a pseudofunctor coming from an ordinary functor the
morphisms of `∫ᶜ F` whose fibre component is a transport are compared by nothing more than the
bookkeeping of transports.

## Main results

* `CategoryTheory.Functor.exists_factor_of_isStronglyCartesian`: a morphism lying over `χ ≫ g`
  factors through a strongly cartesian morphism over `g`, by a morphism over `χ`.
* `CategoryTheory.Functor.isHomLift_comp'`,
  `CategoryTheory.Functor.isStronglyCartesian_comp'`,
  `CategoryTheory.Functor.isStronglyCartesian_of_comp'`,
  `CategoryTheory.Functor.eq_of_isStronglyCartesian_comp_eq`,
  `CategoryTheory.Functor.isHomLift_map_of_comp_eq_of`,
  `CategoryTheory.Functor.exists_isoOverId_of_isStronglyCartesian'` and
  `CategoryTheory.Functor.isStronglyCartesian_map_of_comp_eq`: the composition, cancellation and
  transport rules for lying over and being strongly cartesian, with their hypotheses taken as
  explicit arguments rather than as instances.
* `CategoryTheory.Functor.comp_map_eq_of_frameChange`: two strongly cartesian morphisms of the
  target presenting one object through two objects of the source agree on a pair of morphisms as
  soon as they agree on one pair and the two frames are compared in the source.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.exists_isoOverId_of_isStronglyCartesian`: a
  strongly cartesian morphism over `χ` into the image of an object of a fibre is the chosen
  cartesian lift of `χ` composed, on the left, with an isomorphism over an identity.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.isHomLift_ι_map`: a vertical morphism lies over an
  identity.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.ι_map_comp_cartesianLift`: the normal form is the
  vertical morphism of its fibre component followed by the chosen cartesian lift.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.exists_eqToHom_fiber_comp`,
  `CategoryTheory.Pseudofunctor.CoGrothendieck.exists_eqToHom_fiber_cartesianLift` and
  `CategoryTheory.Pseudofunctor.CoGrothendieck.exists_eqToHom_fiber_homOf`: the morphisms whose
  fibre component is a transport are closed under composition and contain the chosen cartesian
  lifts and the normal forms with transport fibre component.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.ι_map_eqToHom_comp_eq`: two morphisms with the same
  base and with transport fibre components, out of two objects of one fibre with equal fibre
  components, differ by the vertical morphism of that equality.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.cartesianLift_comp_homOf_eq`: the normal form of an
  arrow, restricted along a morphism of the base, read through a frame change.
* `CategoryTheory.Pseudofunctor.CoGrothendieck.isStronglyCartesian_homOf_of_isIso`: a normal form
  with invertible fibre component is strongly cartesian.

## References

* [Stacks Project, Tag 003T](https://stacks.math.columbia.edu/tag/003T)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace CategoryTheory.Functor

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- **A morphism lying over a composite `χ ≫ g` factors through a strongly cartesian morphism
over `g`**, by a morphism lying over `χ`. -/
theorem exists_factor_of_isStronglyCartesian {p : 𝒳 ⥤ 𝒞} {R S T : 𝒞} (χ : R ⟶ S) (g : S ⟶ T)
    {b c : 𝒳} (ρ : b ⟶ c) (hρ : p.IsStronglyCartesian g ρ) {w : 𝒳} (θ : w ⟶ c)
    (hθ : p.IsHomLift (χ ≫ g) θ) :
    ∃ lam : w ⟶ b, p.IsHomLift χ lam ∧ lam ≫ ρ = θ := by
  have h1 := hρ
  have h2 := hθ
  exact ⟨IsStronglyCartesian.map p g ρ (rfl : χ ≫ g = χ ≫ g) θ,
    IsStronglyCartesian.map_isHomLift p g ρ rfl θ,
    IsStronglyCartesian.fac p g ρ rfl θ⟩

/-- **A composite of two morphisms lying over two morphisms of the base lies over the
composite.** The two hypotheses are taken as explicit arguments, so that at a site reached through
a compound term the instances are instantiated rather than synthesised. -/
theorem isHomLift_comp' {p : 𝒳 ⥤ 𝒞} {R S T : 𝒞} {f : R ⟶ S} {g : S ⟶ T} {x y w : 𝒳}
    {φ : x ⟶ y} {ψ : y ⟶ w} (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift g ψ) :
    p.IsHomLift (f ≫ g) (φ ≫ ψ) := by
  have h1 := hφ
  have h2 := hψ
  exact IsHomLift.comp p f g φ ψ

/-- **A composite of two strongly cartesian morphisms is strongly cartesian over the composite**,
with the two hypotheses taken as explicit arguments. -/
@[sga "1 VI 6.13" "more general", sga "4 VI 6.4" "Fr1"]
theorem isStronglyCartesian_comp' {p : 𝒳 ⥤ 𝒞} {R S T : 𝒞} {f : R ⟶ S} {g : S ⟶ T} {x y w : 𝒳}
    {φ : x ⟶ y} {ψ : y ⟶ w} (hφ : p.IsStronglyCartesian f φ) (hψ : p.IsStronglyCartesian g ψ) :
    p.IsStronglyCartesian (f ≫ g) (φ ≫ ψ) := by
  have h1 := hφ
  have h2 := hψ
  exact IsStronglyCartesian.comp p

/-- **The first factor of a strongly cartesian composite whose second factor is strongly cartesian
is strongly cartesian**, with the hypotheses taken as explicit arguments. -/
@[sga "1 VI 6.13" "more general"]
theorem isStronglyCartesian_of_comp' {p : 𝒳 ⥤ 𝒞} {R S T : 𝒞} {f : R ⟶ S} {g : S ⟶ T} {x y w : 𝒳}
    {φ : x ⟶ y} {ψ : y ⟶ w} (hcomp : p.IsStronglyCartesian (f ≫ g) (φ ≫ ψ))
    (hψ : p.IsStronglyCartesian g ψ) (hφ : p.IsHomLift f φ) : p.IsStronglyCartesian f φ := by
  have h1 := hcomp
  have h2 := hψ
  have h3 := hφ
  exact IsStronglyCartesian.of_comp p (f := f) (g := g) (φ := φ) (ψ := ψ)

/-- **A strongly cartesian morphism is a monomorphism against morphisms lying over one morphism of
the base**, with the hypotheses taken as explicit arguments. -/
theorem eq_of_isStronglyCartesian_comp_eq {p : 𝒳 ⥤ 𝒞} {R S R' : 𝒞} {f : R ⟶ S} {x b : 𝒳}
    {ρ : x ⟶ b} (hρ : p.IsStronglyCartesian f ρ) {g : R' ⟶ R} {w : 𝒳} {ψ ψ' : w ⟶ x}
    (hψ : p.IsHomLift g ψ) (hψ' : p.IsHomLift g ψ') (hh : ψ ≫ ρ = ψ' ≫ ρ) : ψ = ψ' := by
  have h1 := hρ
  have h2 := hψ
  have h3 := hψ'
  exact IsStronglyCartesian.ext p f ρ g hh

/-- **Two strongly cartesian morphisms over one morphism of the base with the same target differ
by an isomorphism lying over an identity.** -/
theorem exists_isoOverId_of_isStronglyCartesian' {p : 𝒳 ⥤ 𝒞} {R S : 𝒞} {f : R ⟶ S} {x y w : 𝒳}
    (φ : x ⟶ w) (hφ : p.IsStronglyCartesian f φ) (ψ : y ⟶ w)
    (hψ : p.IsStronglyCartesian f ψ) :
    ∃ e : x ⟶ y, IsIso e ∧ p.IsHomLift (𝟙 R) e ∧ e ≫ ψ = φ := by
  have h1 := hψ
  have h2 := hφ
  have hrefl : f = (Iso.refl R).hom ≫ f := by simp
  refine ⟨(IsStronglyCartesian.domainIsoOfBaseIso p hrefl ψ φ).hom, inferInstance, ?_, ?_⟩
  · exact IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift p hrefl ψ φ
  · exact IsStronglyCartesian.fac p f ψ hrefl φ

/-- **A functor strictly over the base transports lying over a morphism of the base**, with the
hypothesis taken as an explicit argument and with independent hom universes. -/
theorem isHomLift_map_of_comp_eq_of {𝒟 : Type u₃} [Category.{v₃} 𝒟] {p : 𝒳 ⥤ 𝒞} {q : 𝒟 ⥤ 𝒞}
    {N : 𝒳 ⥤ 𝒟} (hN : N ⋙ q = p) {R T : 𝒞} (f : R ⟶ T) {aa bb : 𝒳} (φ : aa ⟶ bb)
    (hφ : p.IsHomLift f φ) : q.IsHomLift f (N.map φ) := by
  have h1 := hφ
  exact isHomLift_map_of_comp_eq hN f φ

/-- **A functor over `u` carrying strongly cartesian morphisms to strongly cartesian morphisms
sends a morphism strongly cartesian over `d` to one strongly cartesian over `u(d)`.** -/
theorem isStronglyCartesian_map_of_comp_eq {𝒟 : Type u₃} [Category.{v₃} 𝒟] {𝒯 : Type u₄}
    [Category.{v₄} 𝒯] {p : 𝒳 ⥤ 𝒞} {q : 𝒯 ⥤ 𝒟} {u : 𝒞 ⥤ 𝒟} {F : 𝒳 ⥤ 𝒯} (hF : F ⋙ q = p ⋙ u)
    (hFsc : ∀ {x y : 𝒳} (α : x ⟶ y), q.IsStronglyCartesian ((p ⋙ u).map α) (F.map α))
    {W U : 𝒞} {dd : W ⟶ U} {x y : 𝒳} {ex : x ⟶ y} (hex : p.IsStronglyCartesian dd ex) :
    q.IsStronglyCartesian (u.map dd) (F.map ex) := by
  have hexl : (p ⋙ u).IsHomLift (u.map dd) ex :=
    isHomLift_comp_functor u dd ex hex.toIsHomLift
  exact isStronglyCartesian_of_isHomLift (hFsc ex) (u.map dd)
    (isHomLift_map_of_comp_eq hF (u.map dd) ex)

/-- **A morphism of the source read through two frames of one object of the target.** Let `N` be
a 1-morphism of fibred categories, let `A` and `B` be strongly cartesian morphisms of `𝒯` over
`β'` and `χ₂` out of one object, into the images of two objects of `𝒳`, let `sa` and `sb` be
strongly cartesian morphisms of `𝒳` over `β'` and `χ₂` out of one object, and let `v₀` be a
morphism of `𝒳` over an identity comparing the two. If the two frames agree on one pair of
morphisms `g₁`, `g₂` into a common target, both in `𝒳` and after `N`, then they agree on every
pair `h₁`, `h₂` on which they agree in `𝒳`.

The frames differ by an isomorphism over an identity, which `v₀` computes because the composite
`sb ≫ g₂` is strongly cartesian and therefore cancels. -/
theorem comp_map_eq_of_frameChange {𝒯 : Type u₄} [Category.{v₄} 𝒯] {p : 𝒳 ⥤ 𝒞} {r : 𝒯 ⥤ 𝒞}
    {N : 𝒳 ⥤ 𝒯} (hN : p.IsFibredOneMorphism r N)
    {V' V₁ T₂ Uc : 𝒞} {β' : V' ⟶ V₁} {χ₂ : V' ⟶ T₂} {k : V' ⟶ Uc}
    {X Xb Ya Yb Yc Yd : 𝒳} {sa : X ⟶ Ya} {sb : Xb ⟶ Yb} {v₀ : X ⟶ Xb}
    {g₁ : Ya ⟶ Yc} {g₂ : Yb ⟶ Yc} {h₁ : Ya ⟶ Yd} {h₂ : Yb ⟶ Yd}
    (hsa : p.IsStronglyCartesian β' sa) (hsb : p.IsStronglyCartesian χ₂ sb)
    (hv₀ : p.IsHomLift (𝟙 V') v₀) (hm : p.IsStronglyCartesian k (sb ≫ g₂))
    (hid1 : sa ≫ g₁ = v₀ ≫ sb ≫ g₂) (hid2 : sa ≫ h₁ = v₀ ≫ sb ≫ h₂)
    {z : 𝒯} {A : z ⟶ N.obj Ya} (hA : r.IsStronglyCartesian β' A)
    {Bb : z ⟶ N.obj Yb} (hBb : r.IsStronglyCartesian χ₂ Bb)
    (hdag : A ≫ N.map g₁ = Bb ≫ N.map g₂) :
    A ≫ N.map h₁ = Bb ≫ N.map h₂ := by
  have hNsa : r.IsStronglyCartesian β' (N.map sa) := hN.map_isStronglyCartesian β' sa hsa
  have hNsb : r.IsStronglyCartesian χ₂ (N.map sb) := hN.map_isStronglyCartesian χ₂ sb hsb
  have hNm : r.IsStronglyCartesian k (N.map (sb ≫ g₂)) :=
    hN.map_isStronglyCartesian k (sb ≫ g₂) hm
  obtain ⟨ι₁, hι₁iso, hι₁lift, hι₁fac⟩ :=
    exists_isoOverId_of_isStronglyCartesian' A hA (N.map sa) hNsa
  obtain ⟨ι₂, hι₂iso, hι₂lift, hι₂fac⟩ :=
    exists_isoOverId_of_isStronglyCartesian' Bb hBb (N.map sb) hNsb
  have hNv₀lift : r.IsHomLift (𝟙 V') (N.map v₀) :=
    isHomLift_map_of_comp_eq_of hN.comp_eq (𝟙 V') v₀ hv₀
  have hlift : r.IsHomLift (𝟙 V') (ι₁ ≫ N.map v₀) := by
    have h0 := isHomLift_comp' hι₁lift hNv₀lift
    rwa [Category.comp_id] at h0
  have hfr : ι₁ ≫ N.map v₀ = ι₂ := by
    refine eq_of_isStronglyCartesian_comp_eq hNm hlift hι₂lift ?_
    rw [Category.assoc, ← N.map_comp, ← hid1, N.map_comp, ← Category.assoc, hι₁fac, hdag,
      ← hι₂fac, Category.assoc, ← N.map_comp]
  rw [← hι₁fac, ← hι₂fac, Category.assoc, Category.assoc, ← N.map_comp, ← N.map_comp, hid2,
    N.map_comp, ← Category.assoc, hfr]

end CategoryTheory.Functor

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

section Attachment

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]
  {F : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat.{v₂, u₂}}
  {𝒯 : Type u₄} [Category.{v₃} 𝒯] {r : 𝒯 ⥤ 𝒮} {N : CoGrothendieck F ⥤ 𝒯}

/-- **A strongly cartesian morphism over `χ` into the image of an object of a fibre is the image
of the chosen cartesian lift of `χ`, precomposed with an isomorphism over an identity.** The image
of the chosen cartesian lift is strongly cartesian over `χ` as well, and two strongly cartesian
morphisms over one morphism of the base with the same target differ by such an isomorphism. -/
theorem exists_isoOverId_of_isStronglyCartesian (hN : (forget F).IsFibredOneMorphism r N)
    {V T : 𝒮} (χ : V ⟶ T) {b : F.obj ⟨op T⟩} {z : 𝒯} (κ : z ⟶ N.obj ⟨T, b⟩)
    (hκ : r.IsStronglyCartesian χ κ) :
    ∃ ι₀ : z ⟶ N.obj ⟨V, (F.map χ.op.toLoc).toFunctor.obj b⟩,
      IsIso ι₀ ∧ r.IsHomLift (𝟙 V) ι₀ ∧ ι₀ ≫ N.map (cartesianLift b χ) = κ := by
  have hcL : r.IsStronglyCartesian χ (N.map (cartesianLift b χ)) :=
    hN.map_isStronglyCartesian χ _ (isStronglyCartesian_homCartesianLift b χ)
  exact Functor.exists_isoOverId_of_isStronglyCartesian' κ hκ _ hcL

/-- **A vertical morphism of `∫ᶜ F` lies over an identity.** -/
theorem isHomLift_ι_map {V : 𝒮} {c c' : F.obj ⟨op V⟩} (ε : c ⟶ c') :
    (forget F).IsHomLift (𝟙 V) ((ι F V).map ε) :=
  Functor.IsHomLift.map ((ι F V).map ε)

/-- The fibre component of the chosen cartesian lift is a transport: it is an identity. -/
theorem exists_eqToHom_fiber_cartesianLift {V T : 𝒮} (g : V ⟶ T) (b : F.obj ⟨op T⟩) :
    ∃ p, (cartesianLift b g).fiber = eqToHom p := exists_eqToHom_id _

/-- The fibre component of a normal form with transport fibre component is a transport. -/
theorem exists_eqToHom_fiber_homOf {V T : 𝒮} (g : V ⟶ T) {c : F.obj ⟨op V⟩} {b : F.obj ⟨op T⟩}
    {γ : c ⟶ (F.map g.op.toLoc).toFunctor.obj b} (hγ : ∃ p, γ = eqToHom p) :
    ∃ p, (homOf g γ).fiber = eqToHom p := hγ

end Attachment

section Transports

attribute [local implicit_reducible] Functor.toPseudofunctor'
  pseudofunctorOfIsLocallyDiscrete Quiver.Hom.toLoc

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] (K : 𝒞ᵒᵖ ⥤ Cat.{v₂, u₂})

/-- The unit constraint of the pseudofunctor attached to an ordinary functor into a strict
bicategory is a transport. -/
theorem exists_eqToHom_mapId_inv (X : LocallyDiscrete 𝒞ᵒᵖ) (x : K.toPseudofunctor'.obj X) :
    ∃ p, (K.toPseudofunctor'.mapId X).inv.toNatTrans.app x = eqToHom p :=
  ⟨_, by rw [Functor.toPseudofunctor'_mapId, eqToIso.inv, Cat.eqToHom_app]⟩

/-- The composition constraint of the pseudofunctor attached to an ordinary functor into a strict
bicategory is a transport. -/
theorem exists_eqToHom_mapComp_inv {X Y Z : LocallyDiscrete 𝒞ᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : K.toPseudofunctor'.obj X) :
    ∃ p, (K.toPseudofunctor'.mapComp f g).inv.toNatTrans.app x = eqToHom p :=
  ⟨_, by rw [Functor.toPseudofunctor'_mapComp, eqToIso.inv, Cat.eqToHom_app]⟩

/-- **The normal form is the vertical morphism of its fibre component followed by the chosen
cartesian lift.** Both sides have the same base after cancelling an identity, and their fibre
components differ by the unit and composition constraints, which are transports. -/
theorem ι_map_comp_cartesianLift {V T : 𝒞} (g : V ⟶ T) {c : K.toPseudofunctor'.obj ⟨op V⟩}
    {b : K.toPseudofunctor'.obj ⟨op T⟩}
    (γ : c ⟶ (K.toPseudofunctor'.map g.op.toLoc).toFunctor.obj b) :
    (ι K.toPseudofunctor' V).map γ ≫ cartesianLift b g = homOf g γ := by
  have hbL : ((ι K.toPseudofunctor' V).map γ ≫ cartesianLift b g).base = 𝟙 V ≫ g := rfl
  have hL : ((ι K.toPseudofunctor' V).map γ ≫ cartesianLift b g).fiber =
      (γ ≫ (K.toPseudofunctor'.mapId ⟨op V⟩).inv.toNatTrans.app
          ((K.toPseudofunctor'.map g.op.toLoc).toFunctor.obj b)) ≫
        (K.toPseudofunctor'.map (𝟙 V).op.toLoc).toFunctor.map
            (𝟙 ((K.toPseudofunctor'.map g.op.toLoc).toFunctor.obj b)) ≫
          (K.toPseudofunctor'.mapComp g.op.toLoc (𝟙 V).op.toLoc).inv.toNatTrans.app b := rfl
  refine Hom.ext _ _ (hbL.trans (Category.id_comp g)) ?_
  rw [hL]
  simp only [Category.assoc]
  refine congrArg (fun t => γ ≫ t) ?_
  refine eq_of_exists_eqToHom (exists_eqToHom_comp (exists_eqToHom_mapId_inv K _ _)
    (exists_eqToHom_comp (exists_eqToHom_map _ (exists_eqToHom_id _))
      (exists_eqToHom_mapComp_inv K _ _ _))) ⟨_, rfl⟩

/-- **The morphisms whose fibre component is a transport are closed under composition**, the
composition constraint of a pseudofunctor coming from an ordinary functor being a transport. -/
theorem exists_eqToHom_fiber_comp {X Y Z : CoGrothendieck K.toPseudofunctor'}
    (m₁ : X ⟶ Y) (m₂ : Y ⟶ Z)
    (hf₁ : ∃ p, m₁.fiber = eqToHom p) (hf₂ : ∃ p, m₂.fiber = eqToHom p) :
    ∃ p, (m₁ ≫ m₂).fiber = eqToHom p := by
  have hL : (m₁ ≫ m₂).fiber = m₁.fiber ≫
      (K.toPseudofunctor'.map m₁.base.op.toLoc).toFunctor.map m₂.fiber ≫
        (K.toPseudofunctor'.mapComp m₂.base.op.toLoc m₁.base.op.toLoc).inv.toNatTrans.app
          Z.fiber := rfl
  rw [hL]
  exact exists_eqToHom_comp hf₁ (exists_eqToHom_comp (exists_eqToHom_map _ hf₂)
    (exists_eqToHom_mapComp_inv K _ _ _))

/-- **Two morphisms with the same base and with transport fibre components, out of two objects of
one fibre whose fibre components agree, differ by the vertical morphism of that agreement.** Both
composites have the same base, and their fibre components are transports between the same pair of
objects. -/
theorem ι_map_eqToHom_comp_eq {V : 𝒞} {c₁ c₂ : K.toPseudofunctor'.obj ⟨op V⟩} (pc : c₁ = c₂)
    {Y : CoGrothendieck K.toPseudofunctor'}
    (m₁ : (⟨V, c₁⟩ : CoGrothendieck K.toPseudofunctor') ⟶ Y)
    (m₂ : (⟨V, c₂⟩ : CoGrothendieck K.toPseudofunctor') ⟶ Y)
    (hb : m₁.base = m₂.base)
    (hf₁ : ∃ p, m₁.fiber = eqToHom p) (hf₂ : ∃ p, m₂.fiber = eqToHom p) :
    (ι K.toPseudofunctor' V).map (eqToHom pc) ≫ m₂ = m₁ := by
  refine Hom.ext _ _ ((Category.id_comp m₂.base).trans hb.symm) ?_
  have hL : ((ι K.toPseudofunctor' V).map (eqToHom pc) ≫ m₂).fiber =
      (eqToHom pc ≫ (K.toPseudofunctor'.mapId ⟨op V⟩).inv.toNatTrans.app c₂) ≫
        (K.toPseudofunctor'.map (𝟙 V).op.toLoc).toFunctor.map m₂.fiber ≫
          (K.toPseudofunctor'.mapComp m₂.base.op.toLoc (𝟙 V).op.toLoc).inv.toNatTrans.app
            Y.fiber := rfl
  rw [hL]
  refine eq_of_exists_eqToHom ?_ (exists_eqToHom_comp hf₁ ⟨_, rfl⟩)
  exact exists_eqToHom_comp (exists_eqToHom_comp ⟨pc, rfl⟩ (exists_eqToHom_mapId_inv K _ _))
    (exists_eqToHom_comp (exists_eqToHom_map _ hf₂) (exists_eqToHom_mapComp_inv K _ _ _))

/-- **A morphism in normal form out of a restricted object, read through a frame change.**
Suppose the chosen cartesian frame of `V'` through `β'` is compared with a second object `cb` of
the fibre over `V'` by transports `p_v`, `p_v'`, that the second frame carries a morphism `m₂'`
into `⟨T, b'⟩` restricting the composite of the two chosen cartesian lifts, that an arrow `ζ` of
the fibre over `V'` corresponds under the transports to the restriction of `γ` along `β'`, and
that `M` is the composite of `ζ` with `m₂'`. Then the normal form of `γ`, restricted along `β'`,
is the transport followed by `M`. -/
theorem cartesianLift_comp_homOf_eq {V' V₁ T : 𝒞} (β' : V' ⟶ V₁) (χ : V₁ ⟶ T)
    {b b' : K.toPseudofunctor'.obj ⟨op T⟩}
    (γ : (K.toPseudofunctor'.map χ.op.toLoc).toFunctor.obj b ⟶
      (K.toPseudofunctor'.map χ.op.toLoc).toFunctor.obj b')
    {cb cb' : K.toPseudofunctor'.obj ⟨op V'⟩}
    (p_v : (K.toPseudofunctor'.map β'.op.toLoc).toFunctor.obj
      ((K.toPseudofunctor'.map χ.op.toLoc).toFunctor.obj b) = cb)
    (p_v' : (K.toPseudofunctor'.map β'.op.toLoc).toFunctor.obj
      ((K.toPseudofunctor'.map χ.op.toLoc).toFunctor.obj b') = cb')
    (ζ : cb ⟶ cb')
    (m₂' : (⟨V', cb'⟩ : CoGrothendieck K.toPseudofunctor') ⟶ ⟨T, b'⟩)
    (M : (⟨V', cb⟩ : CoGrothendieck K.toPseudofunctor') ⟶ ⟨T, b'⟩)
    (hv₂ : (ι K.toPseudofunctor' V').map (eqToHom p_v') ≫ m₂' =
      cartesianLift ((K.toPseudofunctor'.map χ.op.toLoc).toFunctor.obj b') β' ≫
        cartesianLift b' χ)
    (harr : (K.toPseudofunctor'.map β'.op.toLoc).toFunctor.map γ ≫ eqToHom p_v' =
      eqToHom p_v ≫ ζ)
    (hM : M = (ι K.toPseudofunctor' V').map ζ ≫ m₂') :
    cartesianLift ((K.toPseudofunctor'.map χ.op.toLoc).toFunctor.obj b) β' ≫ homOf χ γ =
      (ι K.toPseudofunctor' V').map (eqToHom p_v) ≫ M := by
  refine Eq.trans (congrArg (fun t =>
    cartesianLift ((K.toPseudofunctor'.map χ.op.toLoc).toFunctor.obj b) β' ≫ t)
    (ι_map_comp_cartesianLift K χ γ).symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ cartesianLift b' χ)
    (cartesianLift_comp_ι_map K β' γ)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (congrArg (fun t => (ι K.toPseudofunctor' V').map
    ((K.toPseudofunctor'.map β'.op.toLoc).toFunctor.map γ) ≫ t) hv₂.symm) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun t => t ≫ m₂')
    (Functor.map_comp (ι K.toPseudofunctor' V') _ _).symm) ?_
  refine Eq.trans (congrArg (fun t => (ι K.toPseudofunctor' V').map t ≫ m₂') harr) ?_
  refine Eq.trans (congrArg (fun t => t ≫ m₂')
    (Functor.map_comp (ι K.toPseudofunctor' V') _ _)) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun t => (ι K.toPseudofunctor' V').map (eqToHom p_v) ≫ t) hM.symm

/-- **A normal form with invertible fibre component is strongly cartesian** over its base: it is
the vertical morphism of the fibre component, which is an isomorphism, followed by the chosen
cartesian lift. -/
theorem isStronglyCartesian_homOf_of_isIso {V T : 𝒞} (g : V ⟶ T)
    {c : K.toPseudofunctor'.obj ⟨op V⟩} {b : K.toPseudofunctor'.obj ⟨op T⟩}
    (γ : c ⟶ (K.toPseudofunctor'.map g.op.toLoc).toFunctor.obj b) (hγ : IsIso γ) :
    (forget K.toPseudofunctor').IsStronglyCartesian g (homOf g γ) := by
  have hι : IsIso ((ι K.toPseudofunctor' V).map γ) := by
    have := hγ
    infer_instance
  have hlift := isHomLift_ι_map γ
  have hvert : (forget K.toPseudofunctor').IsStronglyCartesian (𝟙 V)
      ((ι K.toPseudofunctor' V).map γ) :=
    Functor.IsStronglyCartesian.of_isIso _ (𝟙 V) _
  have hcl : (forget K.toPseudofunctor').IsStronglyCartesian g (cartesianLift b g) :=
    isStronglyCartesian_homCartesianLift b g
  have h := PullbackAdjunction.isStronglyCartesian_id_comp hvert hcl
  rwa [ι_map_comp_cartesianLift K g γ] at h

end Transports

end CategoryTheory.Pseudofunctor.CoGrothendieck

end
