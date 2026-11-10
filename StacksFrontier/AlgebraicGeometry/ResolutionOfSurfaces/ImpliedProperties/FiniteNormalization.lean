module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.Alteration
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.IntegralSchemes
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Japanese
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.ProperFiniteness.GlobalSections
public import StacksFrontier.AlgebraicGeometry.ProperFiniteness.GlobalSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.Topology.Dimension.DimensionFunctionObstruction
public import StacksFrontier.Topology.Noetherian.QuasiCompactLocally

/-!
# Finiteness of normalization from a regular alteration

Let `Y` be an integral locally Noetherian scheme. If `Y` admits an alteration whose source is
regular, then the normalization of `Y` is finite over `Y`.

Finiteness is Zariski-local on the target, so it is enough to check it over an affine open
`U = Spec A` of `Y`. Writing `V` for the preimage of `U`, the restricted morphism `V ⟶ Spec A`
is proper, so `C = Γ(V, ⊤)` is a finite `A`-module; `V` is regular, hence normal, so `C` is an
integrally closed domain, and the integral closure `B` of `A` in its fraction field therefore
sits inside `C` and is finite over the Noetherian ring `A`. Over `U` the normalization is
`Spec B ⟶ Spec A`.

## Main results

* `AlgebraicGeometry.normalization_isFinite_of_regular_alteration`: the normalization of an
  integral locally Noetherian scheme admitting a regular alteration is finite.

## Implementation notes

The step "`C` is a finite `A`-module" is the degree-zero case of [Stacks, Tag 02O6] for the
structure sheaf, named `AlgebraicGeometry.FiniteGlobalSectionsOfProper` in
`StacksFrontier.AlgebraicGeometry.ProperFiniteness.GlobalSections` and proved, with no hypothesis,
by `AlgebraicGeometry.finiteGlobalSectionsOfProper` in
`StacksFrontier.AlgebraicGeometry.ProperFiniteness.GlobalSectionsFinite`. It is used once, and the
conclusion below is therefore unconditional. The companion assertion of [Stacks, Tag 0BGG], that
`Y` has a dense regular open, is `AlgebraicGeometry.exists_dense_open_isRegular` in the sibling
module; the two together are the tag's covering set.

The normalization morphism requires finiteness of the irreducible components of every
quasi-compact open. A quasi-compact open of a locally Noetherian scheme is a Noetherian space,
so that hypothesis is produced inside the statement by a `let` rather than carried as an
argument; this also makes the normalization morphism the statement names unambiguous.

`finiteProp` names finiteness at type `MorphismProperty Scheme`. Naming it there rather than
letting `IsFinite` be read as one at the point of use is what lets the affine-locality and
Zariski-locality interfaces apply, and keeps the two transports below — along an isomorphism of
arrows and along an open cover — ordinary instance resolution.

## References

* [Stacks Project, Tag 0BGG](https://stacks.math.columbia.edu/tag/0BGG)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

/-- The integral closure of a Noetherian domain in its fraction field is finite over it as soon
as the domain admits a finite integrally closed domain extension with injective structure map. -/
private theorem integralClosure_finite_of_finite_integrallyClosed
    (A C : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing C] [IsDomain C] [Algebra A C] [IsScalarTower A C (FractionRing C)]
    [IsFractionRing C (FractionRing C)] [IsIntegrallyClosed C]
    (hAC : Function.Injective (algebraMap A C)) [Module.Finite A C] :
    Module.Finite A ↥(integralClosure A (FractionRing A)) := by
  let K := FractionRing A
  let L := FractionRing C
  have hAL : Function.Injective (algebraMap A L) := (IsFractionRing.injective C L).comp hAC
  let e : K →+* L := IsFractionRing.lift hAL
  let eA : K →ₐ[A] L := { toRingHom := e, commutes' := fun a => by simp [e] }
  let B := integralClosure A K
  let j := (IsScalarTower.toAlgHom A C L).toLinearMap
  let φ : B →ₗ[A] LinearMap.range j :=
    (eA.toLinearMap ∘ₗ B.val.toLinearMap).codRestrict _ fun b => LinearMap.mem_range.mpr <|
      (isIntegrallyClosed_iff L).mp inferInstance (IsIntegral.map eA b.2).tower_top
  have hφ : Function.Injective φ := fun x y h =>
    Subtype.ext (RingHom.injective e (congrArg Subtype.val h))
  exact Module.Finite.of_injective
    ((LinearEquiv.ofInjective j (IsFractionRing.injective C L)).symm.toLinearMap ∘ₗ φ)
    ((LinearEquiv.ofInjective j (IsFractionRing.injective C L)).symm.injective.comp hφ)

namespace AlgebraicGeometry

/-- Every point of a scheme has an affine open neighbourhood. -/
private theorem exists_affineOpen_mem (Y : Scheme.{u}) (x : Y) :
    ∃ U : Y.affineOpens, x ∈ U.1 := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨W, hW⟩, hxW⟩

/-- A morphism of schemes is finite if and only if, over every affine open of the target, the
preimage is affine and the induced ring map is finite. -/
local instance hasAffinePropertyFiniteProp :
    HasAffineProperty finiteProp.{u} (affineAnd RingHom.Finite) := by
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan]
  intro X Y f
  simp [finiteProp, isFinite_iff]

/-- The affine property "the source is affine and the ring map is finite" is local on the
target. -/
local instance : (affineAnd RingHom.Finite).IsLocal.{u} :=
  (inferInstance :
    HasAffineProperty finiteProp.{u} (affineAnd RingHom.Finite)).isLocal_affineProperty

/-- The normalization of an integral locally Noetherian scheme with a regular alteration is
finite over an affine open of the target. -/
private theorem normalization_restrict_isFinite_of_regular_alteration
    (Y X : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (hf : IsAlteration f) (hX : IsRegular X)
    (hfinite : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (U : Y.affineOpens) [Nonempty U.1] :
    (affineAnd RingHom.Finite) (Scheme.normalization Y hfinite ∣_ U.1) := by
  let V : X.Opens := f ⁻¹ᵁ U.1
  have : IsIntegral X := hf.2.2.1
  have hgeneric := ((tfae_isDominant_of_isIntegral f).out 1 2).mp hf.2.1
  have hηV : genericPoint X ∈ V := by
    change f (genericPoint X) ∈ U.1
    rw [hgeneric]
    exact (genericPoint_spec Y).mem_open_set_iff U.1.2 |>.mpr (by simpa using ‹Nonempty U.1›)
  have : Nonempty V := ⟨⟨genericPoint X, hηV⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have hV : IsRegular V.toScheme := IsRegular.restrict hX V
  have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isRegular hV
  let A := Γ(Y, U.1)
  let C := Γ(V.toScheme, ⊤)
  let e : Spec (.of A) ≅ U.1.toScheme := U.2.isoSpec.symm
  let g : V.toScheme ⟶ Spec (.of A) := (f ∣_ U.1) ≫ e.inv
  have hA : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  have : IsDomain A := IsIntegral.component_integral U.1
  have : Nonempty (⊤ : V.toScheme.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty V), by simp⟩⟩
  have : IsDomain C := IsIntegral.component_integral (⊤ : V.toScheme.Opens)
  let : Algebra A C := ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom.toAlgebra
  have : IsIntegrallyClosed C := by
    have : IsNormal V.toScheme := isNormal_of_isRegular V.toScheme hV
    exact normal_globalSections V.toScheme
  have hC : Module.Finite A C := by
    have : IsProper (f ∣_ U.1) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f U.1).flip hf.1
    exact module_finite_globalSections g (finiteGlobalSectionsOfProper A hA g inferInstance)
  have hAC : Function.Injective (algebraMap A C) := by
    have hVdense : Dense (V : Set X) := by
      have hηdense : Dense ({genericPoint X} : Set X) := by
        rw [dense_iff_closure_eq, (genericPoint_spec X).def]
      exact hηdense.mono (Set.singleton_subset_iff.mpr hηV)
    have : IsDominant V.ι := Opens.isDominant_ι hVdense
    have : IsDominant f := hf.2.1
    have : IsDominant ((f ∣_ U.1) ≫ U.1.ι) := by
      rw [morphismRestrict_ι]
      infer_instance
    have : IsDominant (f ∣_ U.1) := IsDominant.of_comp_of_isOpenImmersion (f ∣_ U.1) U.1.ι
    obtain ⟨x⟩ : Nonempty V := inferInstance
    obtain ⟨W, hxW⟩ := exists_affineOpen_mem V.toScheme x
    have hWtop : W.1 ≤ (⊤ : V.toScheme.Opens) := le_top
    have hinj := ((tfae_isDominant_of_isIntegral g).out 1 4).mp (inferInstance : IsDominant g)
    have hinjW : Function.Injective (g.appLE ⊤ W.1 hWtop) :=
      hinj W ⟨⊤, isAffineOpen_top (Spec (.of A))⟩ ⟨⟨x, hxW⟩⟩
        ⟨⟨genericPoint (Spec (.of A)), Set.mem_univ _⟩⟩ fun _ _ => trivial
    intro a b hab
    apply (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.injective
    apply hinjW
    change (V.toScheme.presheaf.map (homOfLE hWtop).op).hom
        (((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom a) =
      (V.toScheme.presheaf.map (homOfLE hWtop).op).hom
        (((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom b)
    exact congrArg (V.toScheme.presheaf.map (homOfLE hWtop).op).hom hab
  have : Module.Finite A (integralClosure A (FractionRing A)) :=
    integralClosure_finite_of_finite_integrallyClosed A C hAC
  have hSpec : IsFinite (Spec.map
      (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  let νU := preimageNormalizationIsoSpecIntegralClosure hfinite U.1 e
  let arrowIso :
      CategoryTheory.Arrow.mk (Scheme.normalization Y hfinite ∣_ U.1) ≅
        CategoryTheory.Arrow.mk
          (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))))) :=
    CategoryTheory.Arrow.isoMk νU e.symm (by
      simpa [νU, A] using preimageNormalizationIsoSpecIntegralClosure_hom_comp
        (X := Y) (hX := hfinite) (U := U.1) (e := e))
  exact (affineAnd RingHom.Finite).arrow_mk_iso_iff arrowIso |>.mpr
    ((HasAffineProperty.iff_of_isAffine (P := finiteProp.{u})).mp hSpec)

/-- **The normalization of an integral locally Noetherian scheme admitting an alteration by a
regular scheme is finite.** This is the first assertion of [Stacks, Tag 0BGG]. The one input of
the source's argument beyond this module is the degree-zero case of [Stacks, Tag 02O6] for the
structure sheaf, which enters once as `AlgebraicGeometry.finiteGlobalSectionsOfProper`; the
statement is therefore unconditional.

The source assumes `Y` Noetherian, i.e. locally Noetherian and quasi-compact. Quasi-compactness
is not used: finiteness is Zariski-local on the target, and the argument runs over one affine
open at a time. -/
@[stacks 0BGG "finiteness of the normalization"]
theorem normalization_isFinite_of_regular_alteration
    (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (X : Scheme.{u}) (f : X ⟶ Y)
    (hf : IsAlteration f) (hX : IsRegular X) :
    let hY : ∀ U : Y.Opens, IsCompact (U : Set Y) →
        (irreducibleComponents U).Finite := fun U hU ↦ by
      let : CompactSpace U := isCompact_iff_compactSpace.mp hU
      let : NoetherianSpace U :=
        noetherianSpace_of_isLocallyNoetherianSpace U
          (IsLocallyNoetherianSpace.subtype
            (isLocallyNoetherianSpace_of_isLocallyNoetherian Y) U)
      exact NoetherianSpace.finite_irreducibleComponents
    IsFinite (Scheme.normalization Y hY) := by
  intro hY
  choose U hcontains using exists_affineOpen_mem Y
  rw [show IsFinite (Scheme.normalization Y hY) ↔ finiteProp.{u} (Scheme.normalization Y hY) from
    Iff.rfl, HasAffineProperty.iff_of_iSup_eq_top (P := finiteProp.{u})
    (fun x : Y => ⟨U x, (U x).2⟩) (top_unique fun x _ => Opens.mem_iSup.mpr ⟨x, hcontains x⟩)]
  intro x
  have : Nonempty (U x).1 := ⟨⟨x, hcontains x⟩⟩
  exact normalization_restrict_isFinite_of_regular_alteration Y X f hf hX hY (U x)

/-! ### The finite case, which needs no coherence of a proper pushforward

When the alteration is itself a finite morphism, the one step of the argument above that
[Stacks, Tag 02O6] supplies — that `Γ(V, ⊤)` is a finite module over `Γ(Y, U)` — is immediate
from finiteness of the morphism. The conclusion is the special case `[IsFinite f]` of
`normalization_isFinite_of_regular_alteration` above and is no stronger than it; what the
repetition buys is a proof that does not run through [Stacks, Tag 02O6], hence not through the
coherence of a proper pushforward and the witness sheaves behind it. It is the form the argument
is used in on a one-dimensional target, where [Stacks, Tag 0AB7] already makes a proper
generically quasi-finite morphism finite. -/

/-- The normalization of an integral locally Noetherian scheme with a *finite* regular alteration
is finite over an affine open of the target. This repeats
`normalization_restrict_isFinite_of_regular_alteration` with its single appeal to
[Stacks, Tag 02O6] replaced by finiteness of the morphism. -/
private theorem normalization_restrict_isFinite_of_isFinite_regular_alteration
    (Y X : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] (hf : IsAlteration f) (hX : IsRegular X)
    (hfinite : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (U : Y.affineOpens) [Nonempty U.1] :
    (affineAnd RingHom.Finite) (Scheme.normalization Y hfinite ∣_ U.1) := by
  let V : X.Opens := f ⁻¹ᵁ U.1
  have : IsIntegral X := hf.2.2.1
  have hgeneric := ((tfae_isDominant_of_isIntegral f).out 1 2).mp hf.2.1
  have hηV : genericPoint X ∈ V := by
    change f (genericPoint X) ∈ U.1
    rw [hgeneric]
    exact (genericPoint_spec Y).mem_open_set_iff U.1.2 |>.mpr (by simpa using ‹Nonempty U.1›)
  have : Nonempty V := ⟨⟨genericPoint X, hηV⟩⟩
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have hV : IsRegular V.toScheme := IsRegular.restrict hX V
  have : IsLocallyNoetherian V.toScheme := isLocallyNoetherian_of_isRegular hV
  let A := Γ(Y, U.1)
  let C := Γ(V.toScheme, ⊤)
  let e : Spec (.of A) ≅ U.1.toScheme := U.2.isoSpec.symm
  let g : V.toScheme ⟶ Spec (.of A) := (f ∣_ U.1) ≫ e.inv
  have hA : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian ⟨U.1, U.2⟩
  have : IsDomain A := IsIntegral.component_integral U.1
  have : Nonempty (⊤ : V.toScheme.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty V), by simp⟩⟩
  have : IsDomain C := IsIntegral.component_integral (⊤ : V.toScheme.Opens)
  let : Algebra A C := ((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom.toAlgebra
  have : IsIntegrallyClosed C := by
    have : IsNormal V.toScheme := isNormal_of_isRegular V.toScheme hV
    exact normal_globalSections V.toScheme
  have hC : Module.Finite A C := by
    have : IsFinite (f ∣_ U.1) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict f U.1).flip ‹IsFinite f›
    exact module_finite_globalSections g g.finite_appTop
  have hAC : Function.Injective (algebraMap A C) := by
    have hVdense : Dense (V : Set X) := by
      have hηdense : Dense ({genericPoint X} : Set X) := by
        rw [dense_iff_closure_eq, (genericPoint_spec X).def]
      exact hηdense.mono (Set.singleton_subset_iff.mpr hηV)
    have : IsDominant V.ι := Opens.isDominant_ι hVdense
    have : IsDominant f := hf.2.1
    have : IsDominant ((f ∣_ U.1) ≫ U.1.ι) := by
      rw [morphismRestrict_ι]
      infer_instance
    have : IsDominant (f ∣_ U.1) := IsDominant.of_comp_of_isOpenImmersion (f ∣_ U.1) U.1.ι
    obtain ⟨x⟩ : Nonempty V := inferInstance
    obtain ⟨W, hxW⟩ := exists_affineOpen_mem V.toScheme x
    have hWtop : W.1 ≤ (⊤ : V.toScheme.Opens) := le_top
    have hinj := ((tfae_isDominant_of_isIntegral g).out 1 4).mp (inferInstance : IsDominant g)
    have hinjW : Function.Injective (g.appLE ⊤ W.1 hWtop) :=
      hinj W ⟨⊤, isAffineOpen_top (Spec (.of A))⟩ ⟨⟨x, hxW⟩⟩
        ⟨⟨genericPoint (Spec (.of A)), Set.mem_univ _⟩⟩ fun _ _ => trivial
    intro a b hab
    apply (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv.injective
    apply hinjW
    change (V.toScheme.presheaf.map (homOfLE hWtop).op).hom
        (((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom a) =
      (V.toScheme.presheaf.map (homOfLE hWtop).op).hom
        (((Scheme.ΓSpecIso (.of A)).inv ≫ g.appTop).hom b)
    exact congrArg (V.toScheme.presheaf.map (homOfLE hWtop).op).hom hab
  have : Module.Finite A (integralClosure A (FractionRing A)) :=
    integralClosure_finite_of_finite_integrallyClosed A C hAC
  have hSpec : IsFinite (Spec.map
      (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))))) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  let νU := preimageNormalizationIsoSpecIntegralClosure hfinite U.1 e
  let arrowIso :
      CategoryTheory.Arrow.mk (Scheme.normalization Y hfinite ∣_ U.1) ≅
        CategoryTheory.Arrow.mk
          (Spec.map (CommRingCat.ofHom (algebraMap A (integralClosure A (FractionRing A))))) :=
    CategoryTheory.Arrow.isoMk νU e.symm (by
      simpa [νU, A] using preimageNormalizationIsoSpecIntegralClosure_hom_comp
        (X := Y) (hX := hfinite) (U := U.1) (e := e))
  exact (affineAnd RingHom.Finite).arrow_mk_iso_iff arrowIso |>.mpr
    ((HasAffineProperty.iff_of_isAffine (P := finiteProp.{u})).mp hSpec)

/-- **The normalization of an integral locally Noetherian scheme admitting a finite alteration by
a regular scheme is finite.** This is the special case of
`AlgebraicGeometry.normalization_isFinite_of_regular_alteration` for a *finite* alteration, with
a proof that does not appeal to [Stacks, Tag 02O6]: the only use the source's argument makes of
that tag is to see that the sections of the source over the preimage of an affine open are a
finite module over the sections of the target, and for a finite morphism that is immediate. No
tag attribute is attached, the assertion being weaker than the one above, which carries it. -/
theorem normalization_isFinite_of_isFinite_regular_alteration
    (Y : Scheme.{u}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (X : Scheme.{u}) (f : X ⟶ Y) [IsFinite f]
    (hf : IsAlteration f) (hX : IsRegular X) :
    let hY : ∀ U : Y.Opens, IsCompact (U : Set Y) →
        (irreducibleComponents U).Finite := fun U hU ↦ by
      let : CompactSpace U := isCompact_iff_compactSpace.mp hU
      let : NoetherianSpace U :=
        noetherianSpace_of_isLocallyNoetherianSpace U
          (IsLocallyNoetherianSpace.subtype
            (isLocallyNoetherianSpace_of_isLocallyNoetherian Y) U)
      exact NoetherianSpace.finite_irreducibleComponents
    IsFinite (Scheme.normalization Y hY) := by
  intro hY
  choose U hcontains using exists_affineOpen_mem Y
  rw [show IsFinite (Scheme.normalization Y hY) ↔ finiteProp.{u} (Scheme.normalization Y hY) from
    Iff.rfl, HasAffineProperty.iff_of_iSup_eq_top (P := finiteProp.{u})
    (fun x : Y => ⟨U x, (U x).2⟩) (top_unique fun x _ => Opens.mem_iSup.mpr ⟨x, hcontains x⟩)]
  intro x
  have : Nonempty (U x).1 := ⟨⟨x, hcontains x⟩⟩
  exact normalization_restrict_isFinite_of_isFinite_regular_alteration Y X f hf hX hY (U x)

end AlgebraicGeometry

end
