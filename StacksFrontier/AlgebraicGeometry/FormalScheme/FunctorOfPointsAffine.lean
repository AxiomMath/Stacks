module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumSurjectivity
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsColimit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Points of a formal spectrum over an affine scheme

Let `A` be an admissible topological ring. A *point of `Spf A` over a scheme `T`* is a morphism
`T → Spf A` of locally topologically ringed spaces, `T` being viewed as a formal scheme through
the functor of Stacks 0AI0. This file proves that over an *affine* `T` every such point factors
through one of the quotients `Spec (A/I)` by an ideal of definition — the affine case of the
colimit formula `h_{Spf A} = colim h_{Spec (A/I)}` of Stacks 0AIE, which was the one hypothesis
left open in `StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsColimit`.

The argument is the source's. A point `g` induces a homomorphism `χ : A → Γ(T, 𝒪_T)` on global
sections; the structure sheaf of `T` seen as a formal scheme is pseudo-discrete and `T` is
quasi-compact, so `Γ(T, 𝒪_T)` is *discrete* and the kernel of `χ` is therefore open. Meeting it
with an ideal of definition gives an ideal of definition `I ⊆ ker χ`, so `χ` factors through
`A/I`, and the resulting morphism `T → Spec (A/I) → Spf A` induces the same homomorphism as `g`.
That identifies it with `g`, because a point of `Spf A` over an affine scheme is determined by
the homomorphism it induces.

## Main results

* `AlgebraicGeometry.spfPresheafOn_pushforward_hom_ext_of_discrete`: two maps
  `𝒪_{Spf A} → b_* F` of presheaves of topological rings that agree on global sections are
  equal, as soon as the sections of `F` over the preimages of the basic opens of `Spf A` are
  discrete.
* `AlgebraicGeometry.ltrs_hom_ext_spfLTRSOn_of_ltrsGlobalSectionsMap_eq` and
  `AlgebraicGeometry.schemeToLTRS_spfLTRSOn_hom_ext_of_ltrsGlobalSectionsMap_eq`: a morphism into
  `Spf A` is determined by the map it induces on global sections; over an affine scheme the
  discreteness hypothesis is automatic.
* `AlgebraicGeometry.map_base_obj_spfBasicOpen_spfLTRSOn`: a point `T → Spf A` pulls the basic open
  `D(a) ∩ Spf A` back to the basic open of the induced global section of `T`.
* `AlgebraicGeometry.exists_factor_spfQuotientPointOn`: **every point of `Spf A` over an affine
  scheme factors through some `Spec (A/I)`.**
* `AlgebraicGeometry.surjective_spfQuotientPointsColimitMap_app_of_isAffine` and
  `AlgebraicGeometry.isLocallySurjective_spfQuotientPointsColimitMap_of_isAdmissible`:
  **Stacks 0AIE**, the colimit formula, with the affine case discharged and hence with no
  hypothesis beyond admissibility.

## Implementation notes

The extensionality statement that drives everything is
`AlgebraicGeometry.spfPresheafOn_pushforward_hom_ext_of_discrete`, a verbatim generalisation of
`AlgebraicGeometry.spfPresheaf_pushforward_hom_ext`: the latter takes the target to be the
structure presheaf of a second formal spectrum, whereas the proof uses only that the target is a
sheaf and that its sections over the preimage of a basic open of `Spf A` are discrete. For a
scheme that discreteness is quasi-compactness of the preimage, and the preimage of
`D(a) ∩ Spf A` is the basic open of the induced global section, hence affine.

## References

* [EGA I, Chapter I, Section 10]
* [Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ)
* [Stacks Project, Tag 0AI1](https://stacks.math.columbia.edu/tag/0AI1)
* [Stacks Project, Tag 0AIE](https://stacks.math.columbia.edu/tag/0AIE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open scoped Topology

universe u

namespace CommRingCat

/-- An isomorphism of rings reflects invertibility: an element is a unit exactly when its image
is. -/
theorem isUnit_hom_apply_iff {R S : CommRingCat.{u}} (e : R ≅ S) (z : R) :
    IsUnit (e.hom.hom z) ↔ IsUnit z := by
  refine ⟨fun hz => ?_, fun hz => RingHom.isUnit_map _ hz⟩
  have h := RingHom.isUnit_map e.inv.hom hz
  rwa [show e.inv.hom (e.hom.hom z) = z from ConcreteCategory.congr_hom e.hom_inv_id z] at h

end CommRingCat

namespace AlgebraicGeometry

open TopologicalRing

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

/-- **Maps of the structure presheaf of a formal spectrum into a pushforward are determined by
their values on global sections.** Let `F` be a sheaf of topological rings on a space `Z` and
`b : Z → Spf A` a continuous map such that the sections of `F` over the preimage of every basic
open of `Spf A` are discrete. Two maps `𝒪_{Spf A} → b_* F` of presheaves of topological rings
agreeing on global sections are equal.

This is `AlgebraicGeometry.spfPresheaf_pushforward_hom_ext` with the target freed from being the
structure presheaf of a second formal spectrum: the only properties of that target used in the
argument are that it is a sheaf and that its sections over the preimage of a basic open are
discrete. -/
theorem spfPresheafOn_pushforward_hom_ext_of_discrete (I₀ : SpfIndex A P) {Z : TopCat.{u}}
    (F : Z.Presheaf TopCommRingCat.{u}) (hF : F.IsSheaf) (b : Z ⟶ spfSpace A)
    (hb : ∀ a : A, DiscreteTopology
      (F.obj (op ((Opens.map b).obj (spfBasicOpen A a)))).α)
    {c c' : spfPresheafOn A P ⟶ b _* F} (hΓ : c.app (op ⊤) = c'.app (op ⊤)) : c = c' := by
  refine TopCat.Sheaf.hom_ext (B := spfBasicOpen A) (spfPresheafOn A P)
    ⟨b _* F, TopCat.Sheaf.pushforward_sheaf_of_sheaf b hF⟩
    (isBasis_spfBasicOpen A) fun a => ?_
  have : DiscreteTopology ((b _* F).obj (op (spfBasicOpen A a))).α := hb a
  refine spfPresheafOn_spfBasicOpen_hom_ext A I₀ a fun t => ?_
  have hres : ∀ d : spfPresheafOn A P ⟶ b _* F,
      (d.app (op (spfBasicOpen A a))).1
          (((spfPresheafOn A P).map (homOfLE (le_top : spfBasicOpen A a ≤ ⊤)).op).1 t)
        = ((b _* F).map (homOfLE (le_top : spfBasicOpen A a ≤ ⊤)).op).1
            ((d.app (op ⊤)).1 t) := fun d =>
    ConcreteCategory.congr_hom (d.naturality (homOfLE (le_top : spfBasicOpen A a ≤ ⊤)).op) t
  rw [hres c, hres c', hΓ]

/-- **Maps of the structure presheaf of a formal spectrum into a pushforward are determined by
their values on global sections.** Let `F` be a sheaf of topological rings on a space `Z` and
`b : Z → Spf A` a continuous map such that the sections of `F` over the preimage of every basic
open of `Spf A` are discrete. Two maps `𝒪_{Spf A} → b_* F` of presheaves of topological rings
agreeing on global sections are equal.

This is `AlgebraicGeometry.spfPresheaf_pushforward_hom_ext` with the target freed from being the
structure presheaf of a second formal spectrum: the only properties of that target used in the
argument are that it is a sheaf and that its sections over the preimage of a basic open are
discrete.

The ideals-of-definition case of `spfPresheafOn_pushforward_hom_ext_of_discrete`. -/
theorem spfPresheaf_pushforward_hom_ext_of_discrete (hA : IsPreAdmissible A) {Z : TopCat.{u}}
    (F : Z.Presheaf TopCommRingCat.{u}) (hF : F.IsSheaf) (b : Z ⟶ spfSpace A)
    (hb : ∀ a : A, DiscreteTopology
      (F.obj (op ((Opens.map b).obj (spfBasicOpen A a)))).α)
    {c c' : spfPresheaf A ⟶ b _* F} (hΓ : c.app (op ⊤) = c'.app (op ⊤)) : c = c' :=
  spfPresheafOn_pushforward_hom_ext_of_discrete (A := A) (P := IsIdealOfDefinition)
    (I₀ := preAdmissibleSpfIndex A hA) (Z := Z) (F := F) (hF := hF) (b := b) (hb := hb) (c := c)
    (c' := c') (hΓ := hΓ)

/-- **A morphism into a formal spectrum is determined by the map it induces on global
sections**, provided the sections of the source over the preimages of the basic opens of
`Spf A` are discrete.

The underlying continuous maps agree by
`AlgebraicGeometry.base_eq_of_ltrsGlobalSectionsMap_eq_spfLTRSOn`, and the comparison maps of
sheaves then agree by `AlgebraicGeometry.spfPresheafOn_pushforward_hom_ext_of_discrete`. -/
@[ega "I 10.4.6" "partial"]
theorem ltrs_hom_ext_spfLTRSOn_of_ltrsGlobalSectionsMap_eq (I₀ : SpfIndex A P) {X : LTRS.{u}}
    {u v : X ⟶ spfLTRSOn A P I₀}
    (hdisc : ∀ a : A, DiscreteTopology
      (X.presheaf.obj (op ((Opens.map u.toHom.base).obj (spfBasicOpen A a)))).α)
    (h : ltrsGlobalSectionsMap u = ltrsGlobalSectionsMap v) : u = v := by
  obtain ⟨⟨ub, uc⟩, uloc⟩ := u
  obtain ⟨⟨vb, vc⟩, vloc⟩ := v
  have hbase : ub = vb := base_eq_of_ltrsGlobalSectionsMap_eq_spfLTRSOn A h
  subst hbase
  exact LocallyTopologicallyRingedSpace.Hom.ext' (PresheafedSpace.hext _ _ rfl (heq_of_eq
    (spfPresheafOn_pushforward_hom_ext_of_discrete A I₀ X.presheaf X.IsSheaf ub hdisc h)))

/-- **A morphism into a formal spectrum is determined by the map it induces on global
sections**, provided the sections of the source over the preimages of the basic opens of
`Spf A` are discrete.

The underlying continuous maps agree by
`AlgebraicGeometry.base_eq_of_ltrsGlobalSectionsMap_eq`, and the comparison maps of sheaves then
agree by `AlgebraicGeometry.spfPresheaf_pushforward_hom_ext_of_discrete`.

The ideals-of-definition case of `ltrs_hom_ext_spfLTRSOn_of_ltrsGlobalSectionsMap_eq`. -/
@[ega "I 10.4.6" "partial"]
theorem ltrs_hom_ext_of_ltrsGlobalSectionsMap_eq (hA : IsPreAdmissible A) {X : LTRS.{u}}
    {u v : X ⟶ spfLTRS A hA}
    (hdisc : ∀ a : A, DiscreteTopology
      (X.presheaf.obj (op ((Opens.map u.toHom.base).obj (spfBasicOpen A a)))).α)
    (h : ltrsGlobalSectionsMap u = ltrsGlobalSectionsMap v) : u = v :=
  ltrs_hom_ext_spfLTRSOn_of_ltrsGlobalSectionsMap_eq (A := A) (P := IsIdealOfDefinition)
    (I₀ := preAdmissibleSpfIndex A hA) (X := X) (u := u) (v := v) (hdisc := hdisc) (h := h)

end

/-! ### Points of a formal spectrum over a scheme -/

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P] (I₀ : SpfIndex A P) (T : Scheme.{u})

/-- A point `u : T → Spf A` of a formal spectrum over a scheme pulls the basic open
`D(a) ∩ Spf A` back to the basic open of the global section of `T` that `a` induces.

A point `y` of `T` is sent into `D(a) ∩ Spf A` exactly when `a` is invertible in the local ring
of `T` at `y`, by `AlgebraicGeometry.notMem_base_asIdeal_iff_isUnit_germ_spfLTRSOn`, and that is
the defining condition of the basic open of the induced global section; pseudo-discretisation does
not change germs. -/
theorem map_base_obj_spfBasicOpen_spfLTRSOn (u : schemeToLTRSObj T ⟶ spfLTRSOn A P I₀) (a : A) :
    (Opens.map u.toHom.base).obj (spfBasicOpen A a)
      = T.basicOpen ((ltrsGlobalSectionsMap u).1 ((spfGammaHomOn A P).1 a)) := by
  set s := (ltrsGlobalSectionsMap u).1 ((spfGammaHomOn A P).1 a) with hs
  refine Opens.ext (Set.ext fun y => ?_)
  have hiso : T.presheaf.germ ⊤ y trivial s
      = (pseudoDiscreteStalkIso T.presheaf y).hom.hom
          ((pseudoDiscrete T.presheaf).germ ⊤ y trivial s) :=
    (ConcreteCategory.congr_hom (germ_pseudoDiscreteStalkIso_hom T.presheaf y ⊤ trivial) s).symm
  calc y ∈ ((Opens.map u.toHom.base).obj (spfBasicOpen A a)).carrier
      ↔ a ∉ (u.toHom.base y).1.asIdeal := Iff.rfl
    _ ↔ IsUnit ((schemeToLTRSObj T).presheaf.germ ⊤ y trivial s) :=
        notMem_base_asIdeal_iff_isUnit_germ_spfLTRSOn A u y a
    _ ↔ IsUnit (T.presheaf.germ ⊤ y trivial s) := by
        rw [hiso]
        exact (CommRingCat.isUnit_hom_apply_iff (pseudoDiscreteStalkIso T.presheaf y) _).symm
    _ ↔ y ∈ (T.basicOpen s).carrier := (T.mem_basicOpen_top s y).symm

/-- The preimage of a basic open of `Spf A` under a point `u : T → Spf A` over an *affine*
scheme is quasi-compact: it is a basic open of `T`, hence an affine open. -/
theorem isCompact_map_base_obj_spfBasicOpen_spfLTRSOn [IsAffine T]
    (u : schemeToLTRSObj T ⟶ spfLTRSOn A P I₀) (a : A) :
    IsCompact ((Opens.map u.toHom.base).obj (spfBasicOpen A a)).carrier := by
  rw [map_base_obj_spfBasicOpen_spfLTRSOn A I₀ T u a]
  exact ((isAffineOpen_top T).basicOpen _).isCompact

/-- **A point of a formal spectrum over an affine scheme is determined by the map it induces on
global sections.** For an affine scheme `T` the preimages of the basic opens of `Spf A` are
affine, hence quasi-compact, so the sections of the pseudo-discretised structure sheaf of `T`
over them are discrete and
`AlgebraicGeometry.ltrs_hom_ext_spfLTRSOn_of_ltrsGlobalSectionsMap_eq` applies. -/
theorem schemeToLTRS_spfLTRSOn_hom_ext_of_ltrsGlobalSectionsMap_eq [IsAffine T]
    {u v : schemeToLTRSObj T ⟶ spfLTRSOn A P I₀}
    (h : ltrsGlobalSectionsMap u = ltrsGlobalSectionsMap v) : u = v :=
  ltrs_hom_ext_spfLTRSOn_of_ltrsGlobalSectionsMap_eq A I₀
    (fun a => isPseudoDiscrete_pseudoDiscrete T.presheaf _
      (isCompact_map_base_obj_spfBasicOpen_spfLTRSOn A I₀ T u a)) h

end

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (hA : IsPreAdmissible A) (T : Scheme.{u})

/-- A point `u : T → Spf A` of a formal spectrum over a scheme pulls the basic open
`D(a) ∩ Spf A` back to the basic open of the global section of `T` that `a` induces.

A point `y` of `T` is sent into `D(a) ∩ Spf A` exactly when `a` is invertible in the local ring
of `T` at `y`, by `AlgebraicGeometry.notMem_base_asIdeal_iff_isUnit_germ`, and that is the
defining condition of the basic open of the induced global section; pseudo-discretisation does
not change germs.

The ideals-of-definition case of `map_base_obj_spfBasicOpen_spfLTRSOn`. -/
theorem map_base_obj_spfBasicOpen (u : schemeToLTRSObj T ⟶ spfLTRS A hA) (a : A) :
    (Opens.map u.toHom.base).obj (spfBasicOpen A a)
      = T.basicOpen ((ltrsGlobalSectionsMap u).1 ((spfGammaHom A).1 a)) :=
  map_base_obj_spfBasicOpen_spfLTRSOn (T := T) (A := A) (P := IsIdealOfDefinition) (u := u) (a := a)
    (I₀ := preAdmissibleSpfIndex A hA)

/-- The preimage of a basic open of `Spf A` under a point `u : T → Spf A` over an *affine*
scheme is quasi-compact: it is a basic open of `T`, hence an affine open.

The ideals-of-definition case of `isCompact_map_base_obj_spfBasicOpen_spfLTRSOn`. -/
theorem isCompact_map_base_obj_spfBasicOpen [IsAffine T]
    (u : schemeToLTRSObj T ⟶ spfLTRS A hA) (a : A) :
    IsCompact ((Opens.map u.toHom.base).obj (spfBasicOpen A a)).carrier :=
  isCompact_map_base_obj_spfBasicOpen_spfLTRSOn (T := T) (A := A) (P := IsIdealOfDefinition)
    (u := u) (a := a) (I₀ := preAdmissibleSpfIndex A hA)

/-- **A point of a formal spectrum over an affine scheme is determined by the map it induces on
global sections.** For an affine scheme `T` the preimages of the basic opens of `Spf A` are
affine, hence quasi-compact, so the sections of the pseudo-discretised structure sheaf of `T`
over them are discrete and
`AlgebraicGeometry.ltrs_hom_ext_of_ltrsGlobalSectionsMap_eq` applies.

The ideals-of-definition case of `schemeToLTRS_spfLTRSOn_hom_ext_of_ltrsGlobalSectionsMap_eq`. -/
theorem schemeToLTRS_hom_ext_of_ltrsGlobalSectionsMap_eq [IsAffine T]
    {u v : schemeToLTRSObj T ⟶ spfLTRS A hA}
    (h : ltrsGlobalSectionsMap u = ltrsGlobalSectionsMap v) : u = v :=
  schemeToLTRS_spfLTRSOn_hom_ext_of_ltrsGlobalSectionsMap_eq (T := T) (A := A)
    (P := IsIdealOfDefinition) (u := u) (v := v) (h := h) (I₀ := preAdmissibleSpfIndex A hA)

end

/-! ### Points over an affine scheme factor through a quotient -/

section

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A]
variable {P : Ideal A → Prop} [IsWeakIdealSystem A P]

omit [IsLinearTopology A A] in
/-- **A point of a formal spectrum over an affine scheme is determined by the induced
homomorphism `A → Γ(T, 𝒪_T)`.** When the canonical map `A → Γ(𝒪)` into the global sections of
the formal spectrum taken along the system is an isomorphism, the induced homomorphism
determines the map on global sections, which by
`AlgebraicGeometry.schemeToLTRS_spfLTRSOn_hom_ext_of_ltrsGlobalSectionsMap_eq` determines the
point.

For the ideals of definition of an admissible ring that isomorphism is Stacks 0AHY; for the weak
ideals of definition of a weakly admissible ring it is
`AlgebraicGeometry.isIso_spfwGammaHom`. -/
theorem schemeToLTRS_hom_ext_of_spfPointGammaHomOn_eq (I₀ : SpfIndex A P)
    (hiso : IsIso (spfGammaHomOn A P)) (T : Scheme.{u})
    [IsAffine T] {u v : schemeToLTRSObj T ⟶ spfLTRSOn A P I₀}
    (h : spfPointGammaHomOn A u = spfPointGammaHomOn A v) : u = v := by
  let := hiso
  refine schemeToLTRS_spfLTRSOn_hom_ext_of_ltrsGlobalSectionsMap_eq A I₀ T ?_
  exact (cancel_epi (spfGammaHomOn A P)).1 (Subtype.ext (congrArg CommRingCat.Hom.hom h))

/-- **A point of a formal spectrum over an affine scheme is determined by the induced
homomorphism `A → Γ(T, 𝒪_T)`.** For an admissible `A` the canonical map
`A → Γ(Spf A, 𝒪_{Spf A})` is an isomorphism by Stacks 0AHY, so the induced homomorphism
determines the map on global sections, which by
`AlgebraicGeometry.schemeToLTRS_hom_ext_of_ltrsGlobalSectionsMap_eq` determines the point.

The ideals-of-definition case of `schemeToLTRS_hom_ext_of_spfPointGammaHomOn_eq`. -/
theorem schemeToLTRS_hom_ext_of_spfPointGammaHom_eq (hA : IsAdmissible A) (T : Scheme.{u})
    [IsAffine T] {u v : schemeToLTRSObj T ⟶ spfLTRS A hA.1}
    (h : spfPointGammaHom A hA.1 u = spfPointGammaHom A hA.1 v) : u = v :=
  schemeToLTRS_hom_ext_of_spfPointGammaHomOn_eq (A := A) (P := IsIdealOfDefinition)
    (I₀ := preAdmissibleSpfIndex A hA.1) (hiso := isIso_spfGammaHom A hA) (T := T) (u := u)
    (v := v) (h := h)

omit [IsLinearTopology A A] in
/-- **Every point of a formal spectrum over an affine scheme factors through one of the
quotients.** Let `T` be an affine scheme. Every morphism `T → Spf A` of locally topologically
ringed spaces factors as `T → Spec (A/I) → Spf A` for some member `I` of the weak ideal system,
provided the canonical map `A → Γ(𝒪)` is an isomorphism.

This is the affine case of the surjectivity half of the colimit formula
`h_{Spf A} = colim h_{Spec (A/I)}` of Stacks 0AIE. The point is that `Γ(T, 𝒪_T)` is *discrete*
for the pseudo-discrete topology, `T` being quasi-compact, so the induced homomorphism
`A → Γ(T, 𝒪_T)` has open kernel; meeting that kernel with a member of the system gives a member
`I` killed by it, so the homomorphism factors through `A/I`, and the resulting morphism
`T → Spec (A/I)` followed by `Spec (A/I) → Spf A` induces the same homomorphism, hence agrees
with the given point by
`AlgebraicGeometry.schemeToLTRS_hom_ext_of_spfPointGammaHomOn_eq`.

Closure of the system under intersection with an open ideal is exactly what the meeting step
consumes, which is why an arbitrary weak ideal system serves: for the ideals of definition of an
admissible ring it is `TopologicalRing.IsIdealOfDefinition.inf_of_isOpen`, and for the weak
ideals of definition of a weakly admissible one it is the intersection clause of Stacks 0AI3. -/
theorem exists_factor_spfQuotientPointOn (I₀ : SpfIndex A P) (hiso : IsIso (spfGammaHomOn A P))
    (T : Scheme.{u}) [IsAffine T] (g : schemeToLTRSObj T ⟶ spfLTRSOn A P I₀) :
    ∃ (I : SpfIndex A P) (a : T ⟶ Spec (spfQuotientOn A I)),
      (schemeToFormalScheme.map a).hom ≫ spfQuotientPointOn A I₀ I = g := by
  set χ : TopCommRingCat.of A ⟶ (schemeToLTRSObj T).presheaf.obj (op ⊤) :=
    spfGammaHomOn A P ≫ ltrsGlobalSectionsMap g with hχ
  have hdisc : DiscreteTopology ((schemeToLTRSObj T).presheaf.obj (op ⊤)).α :=
    isPseudoDiscrete_pseudoDiscrete T.presheaf ⊤ (isAffineOpen_top T).isCompact
  have hker : IsOpen ((RingHom.ker χ.1 : Ideal A) : Set A) := by
    have hset : ((RingHom.ker χ.1 : Ideal A) : Set A) = χ.1 ⁻¹' {0} := by
      ext x; exact RingHom.mem_ker
    rw [hset]
    exact (isOpen_discrete _).preimage χ.2
  set I : SpfIndex A P := spfIndexMeetOpen A I₀ hker with hI
  have hkill : ∀ x ∈ I.1, χ.1 x = 0 := fun _ hx => RingHom.mem_ker.1 hx.2
  set ψ : spfQuotientOn A I ⟶ Γ(T, ⊤) :=
    CommRingCat.ofHom (Ideal.Quotient.lift I.1 χ.1 hkill) with hψ
  refine ⟨I, (ΓSpec.adjunction.homEquiv T (op (spfQuotientOn A I))) ψ.op, ?_⟩
  refine schemeToLTRS_hom_ext_of_spfPointGammaHomOn_eq A I₀ hiso T ?_
  have hg : spfPointGammaHomOn A g = CommRingCat.ofHom χ.1 := rfl
  refine (spfPointGammaHomOn_comp_spfQuotientPointOn A I₀ I _).trans ?_
  rw [hg, spfGammaComponentHomOn, Category.assoc,
    ΓSpecIso_inv_ΓSpec_adjunction_homEquiv (X := T) (B := spfQuotientOn A I) ψ]
  exact CommRingCat.hom_ext (Ideal.Quotient.lift_comp_mk I.1 χ.1 hkill)

/-- **Every point of a formal spectrum over an affine scheme factors through one of the
quotients.** Let `A` be an admissible topological ring and `T` an affine scheme. Every morphism
`T → Spf A` of locally topologically ringed spaces factors as `T → Spec (A/I) → Spf A` for some
ideal of definition `I` of `A`.

This is the affine case of the surjectivity half of the colimit formula
`h_{Spf A} = colim h_{Spec (A/I)}` of Stacks 0AIE. The point is that `Γ(T, 𝒪_T)` is *discrete*
for the pseudo-discrete topology, `T` being quasi-compact, so the induced homomorphism
`A → Γ(T, 𝒪_T)` has open kernel; meeting that kernel with an ideal of definition gives an ideal
of definition `I` killed by it, so the homomorphism factors through `A/I`, and the resulting
morphism `T → Spec (A/I)` followed by `Spec (A/I) → Spf A` induces the same homomorphism, hence
agrees with the given point by
`AlgebraicGeometry.schemeToLTRS_hom_ext_of_spfPointGammaHom_eq`.

The ideals-of-definition case of `exists_factor_spfQuotientPointOn`. -/
theorem exists_factor_spfQuotientPoint (hA : IsAdmissible A) (T : Scheme.{u}) [IsAffine T]
    (g : schemeToLTRSObj T ⟶ spfLTRS A hA.1) :
    ∃ (I : IdealsOfDefinition A) (a : T ⟶ Spec (spfQuotient A I)),
      (schemeToFormalScheme.map a).hom ≫ spfQuotientPoint A hA.1 I = g :=
  exists_factor_spfQuotientPointOn (A := A) (P := IsIdealOfDefinition)
    (I₀ := preAdmissibleSpfIndex A hA.1) (hiso := isIso_spfGammaHom A hA) (T := T) (g := g)

/-- **Stacks 0AIE**, the affine case of the colimit formula. The comparison map
`colim h_{Spec (A/I)} → h_{Spf A}` is surjective on the points over an affine scheme: such a
point factors through one of the quotients by
`AlgebraicGeometry.exists_factor_spfQuotientPointOn`. -/
@[stacks 0AIE "the comparison map of the colimit formula is surjective at an affine test scheme"]
theorem surjective_spfQuotientPointsColimitMap_app_of_isAffine (hA : IsAdmissible A)
    (T : Scheme.{u}) [IsAffine T] :
    Function.Surjective ((spfQuotientPointsColimitMap A hA).app (op T)) := by
  intro φ
  obtain ⟨I, a, ha⟩ := exists_factor_spfQuotientPointOn A (preAdmissibleSpfIndex A hA.1)
    (isIso_spfGammaHom A hA) T φ.hom
  refine ⟨(colimit.ι (spfQuotientPointsDiagram A) (OrderDual.toDual I)).app (op T)
    (schemeToFormalScheme.map a), ?_⟩
  rw [spfQuotientPointsColimitMap_app_ι A hA T (OrderDual.toDual I)
    (schemeToFormalScheme.map a)]
  exact InducedCategory.hom_ext ha

/-- **Stacks 0AIE**, the colimit formula, with no hypothesis beyond admissibility: the
comparison map `colim h_{Spec (A/I)} → h_{Spf A}` is locally surjective for the Zariski
topology. Together with
`AlgebraicGeometry.isLocallyInjective_spfQuotientPointsColimitMap` this is the source's
`h_{Spf A} = colim h_{Spec (A/I)}`, read — as it must be — as an isomorphism of the associated
sheaves.

This discharges the hypothesis of
`AlgebraicGeometry.isLocallySurjective_spfQuotientPointsColimitMap`, which was the affine case,
i.e. the surjectivity half of Stacks 0AHZ. -/
@[stacks 0AIE "the comparison map of the colimit formula is locally surjective, with no \
hypothesis beyond admissibility"]
theorem isLocallySurjective_spfQuotientPointsColimitMap_of_isAdmissible (hA : IsAdmissible A) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology.{u}
      (spfQuotientPointsColimitMap A hA) :=
  isLocallySurjective_spfQuotientPointsColimitMap A hA fun T _hT =>
    surjective_spfQuotientPointsColimitMap_app_of_isAffine A hA T

end

end AlgebraicGeometry

end
