module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.AffineCase
public import StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.CotangentSheafComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The differentials of a morphism of affine schemes, in the coordinate rings

Let `φ : R ⟶ A` be a morphism of commutative rings and let `Spec φ : Spec A ⟶ Spec R` be the
induced morphism of affine schemes. This file identifies the global differentials of `Spec φ`
with the Kähler differentials of `φ` itself, and the sheaf of relative differentials of `Spec φ`
with the quasi-coherent sheaf on `Spec A` associated to those Kähler differentials.

## Main definitions

* `toSpecKaehler` and `fromSpecKaehler` are the two comparisons of the Kähler differentials of
  `φ` with those of the induced map `Γ(Spec R, ⊤) ⟶ Γ(Spec A, ⊤)` on global sections of the
  structure sheaves, and `specKaehlerIso` is the isomorphism they form.
* `topSectionsIso` is [Stacks Project, Tag 01UT] for the pair of affine opens
  `⊤ ≤ (Spec φ) ⁻¹ᵁ ⊤`, in the form of the explicit comparison map.
* `sectionsIso` is the comparison of `A`-modules `Ω[A⁄R] ≅ Γ(Spec A, Ω_{Spec A/Spec R})`.
* `tildeKaehlerIso` is the comparison of `𝒪_{Spec A}`-modules between the quasi-coherent sheaf
  associated to `Ω[A⁄R]` and the sheaf of relative differentials of `Spec φ`.

## Main results

* `isIso_toSpecKaehler`: the Kähler differentials of `φ` and of the induced map on global
  sections of the structure sheaves agree.
* `sectionsIso_d`: the comparison of `A`-modules carries the universal differential of `a : A`
  to the universal relative differential of the corresponding global section of `𝒪_{Spec A}`.
* `existsUnique_sectionsIso`: that compatibility determines the comparison of `A`-modules
  uniquely.
* `toTildeΓ_comp_map_tildeKaehlerIso`: the comparison of sheaves read on global sections and
  composed with the unit of the adjunction is `sectionsIso`.
* `existsUnique_tildeKaehlerIso`: the corresponding compatibility determines the comparison of
  sheaves uniquely.

## Implementation notes

[Stacks Project, Tag 01UT] is proved in
`StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.Surjective` in the shape in which it is
used for an affine chart of an arbitrary morphism: the sections of `Ω_{X/S}` over an affine open
`U` lying over an affine open `V` are the Kähler differentials of `f.appLE V U`, a ring map
between the rings `Γ(S, V)` and `Γ(X, U)` of sections of the structure sheaves. The tag itself,
however, is stated with `U = Spec A` and `V = Spec R`, so in the rings `A` and `R` themselves;
and it is in that shape that the statement feeds the de Rham complex of an affine morphism,
where the whole point is to recognise the answer as a construction performed on `φ`. The gap
between the two shapes is the comparison `AlgebraicGeometry.Scheme.ΓSpecIso`, and closing it is
the content of this file.

The comparison is a square of rings whose vertical maps are the two components of `ΓSpecIso`
and whose horizontal maps are `φ` and the map it induces on global sections; the square
commutes by `AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality`. The map of Kähler differentials
induced by a commutative square is `CommRingCat.KaehlerDifferential.map`, and since the vertical
maps of the square are isomorphisms, the square read in the other direction induces a map back.
Neither composite is an endomorphism of a module in a single `ModuleCat`: the two Kähler
differentials live over different rings, and restriction of scalars along the two components of
`ΓSpecIso` intervenes. Restriction of scalars does not change the underlying module, so the two
composites are identified with identity maps by
`CategoryTheory.ModuleCat.restrictScalarsComp'App` and
`CategoryTheory.ModuleCat.restrictScalarsId'App`, whose underlying maps are the identity; with
that, each composite is an endomorphism of a Kähler differential module and
`CommRingCat.KaehlerDifferential.ext` reduces it to its effect on universal differentials, which
`CommRingCat.KaehlerDifferential.map_d` computes. The two resulting equalities of underlying
maps say that the comparison is bijective, hence an isomorphism.

The `A`-module of global sections of a quasi-coherent sheaf on `Spec A` is
`AlgebraicGeometry.moduleSpecΓFunctor`, which is by construction the sections of the sheaf with
scalars restricted along `(ΓSpecIso A).inv`; that is the same restriction of scalars as the one
appearing in the comparison above, but reached through a chain of definitions rather than
written out, so the two spellings are interconvertible only by unfolding definitions that the
simplifier and `rw` will not unfold. Both `sectionsIso` and `sectionsIso_d` have their statements
in the `moduleSpecΓFunctor` spelling and their proofs in term position, where unification does
the conversion.

Passing from sections to the sheaf is then the counit
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ` of the adjunction between the associated-sheaf
functor and global sections, which is an isomorphism on a quasi-coherent sheaf; quasi-coherence
of `Ω_{X/S}` holds for every morphism of schemes and is
`AlgebraicGeometry.Scheme.Hom.isQuasicoherent_relativeDifferentials`. The counit is taken in the
form `Stacks.AlgebraicGeometry.AffineBaseChangeLocality.tildeΓIso`, whose source is written
through `AlgebraicGeometry.Scheme.Modules.fromTildeΓNatTrans`: the source of the counit itself is
`tilde` of the sections of a sheaf of modules while the target of
`(tilde.functor A).mapIso (sectionsIso φ)` is the associated-sheaf functor applied to
`moduleSpecΓFunctor`, and the two are again interchangeable only by unfolding, so with the
counit in the second spelling the composite can be taken apart by rewriting.

Uniqueness of the comparison of sheaves is uniqueness of the comparison of sections together
with the fact that the correspondence `e ↦ (unit) ≫ Γ(e)` is the hom-set bijection of the
adjunction, hence injective. That is why `existsUnique_tildeKaehlerIso` phrases its
compatibility condition through that composite rather than through sections of the sheaf on
`⊤` directly: in the latter form the condition would have to be transported across the
identification of the sections of an associated sheaf with the module it comes from, which is
the content of the unit.

## What is not done here

Only the degree-one differentials are treated. No exterior power, no de Rham complex and no
comparison of de Rham cohomology with the cohomology of `Ω^•_{A/R}` appears; those need a
comparison of exterior-algebra packages on a single sheaf and a transport of cochain complexes,
neither of which is here. The comparison is not shown to be natural in `φ`, nor compatible with
composition of ring maps or with localisation.

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01UO](https://stacks.math.columbia.edu/tag/01UO)
* [Stacks Project, Tag 01I6](https://stacks.math.columbia.edu/tag/01I6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.AffineDifferentialsIso

section SpecComparison

variable {R A : CommRingCat.{u}} (φ : R ⟶ A)

/-! ### The square of rings -/

/-- The map on global sections of the structure sheaves induced by `Spec φ`, in the shape in
which [Stacks Project, Tag 01UT] is proved: as the map attached by
`AlgebraicGeometry.Scheme.Hom.appLE` to the pair of affine opens `⊤ ≤ (Spec φ) ⁻¹ᵁ ⊤`. -/
noncomputable abbrev specAppLE : Γ(Spec R, ⊤) ⟶ Γ(Spec A, ⊤) :=
  (Spec.map φ).appLE ⊤ ⊤ le_top

/-- The map of global sections attached to the pair of opens `⊤ ≤ (Spec φ) ⁻¹ᵁ ⊤` is the
comorphism of `Spec φ` on the whole spectrum. -/
theorem specAppLE_eq_appTop : specAppLE φ = (Spec.map φ).appTop :=
  Scheme.Hom.appLE_eq_app _

/-- The square of rings comparing `φ` with the map it induces on global sections
of the structure sheaves, with the vertical maps the units of the `Spec`-`Γ` adjunction. -/
theorem ΓSpecIso_inv_comp_specAppLE :
    (Scheme.ΓSpecIso R).inv ≫ specAppLE φ = φ ≫ (Scheme.ΓSpecIso A).inv := by
  rw [specAppLE_eq_appTop, ← Scheme.ΓSpecIso_inv_naturality]

/-- The same square of rings read with the inverse vertical maps. -/
theorem ΓSpecIso_hom_comp_self :
    (Scheme.ΓSpecIso R).hom ≫ φ = specAppLE φ ≫ (Scheme.ΓSpecIso A).hom := by
  rw [specAppLE_eq_appTop, Scheme.ΓSpecIso_naturality]

/-- The two components of `AlgebraicGeometry.Scheme.ΓSpecIso` compose to the identity of `A`,
as a composition of ring homomorphisms. -/
theorem id_eq_ΓSpecIso_hom_comp_inv :
    RingHom.id A = ((Scheme.ΓSpecIso A).hom.hom).comp ((Scheme.ΓSpecIso A).inv.hom) :=
  RingHom.ext fun x => ((Scheme.ΓSpecIso A).inv_hom_id_apply x).symm

/-- The two components of `AlgebraicGeometry.Scheme.ΓSpecIso` compose to the identity of
`Γ(Spec A, ⊤)`, as a composition of ring homomorphisms. -/
theorem id_eq_ΓSpecIso_inv_comp_hom :
    RingHom.id Γ(Spec A, ⊤) = ((Scheme.ΓSpecIso A).inv.hom).comp ((Scheme.ΓSpecIso A).hom.hom) :=
  RingHom.ext fun x => ((Scheme.ΓSpecIso A).hom_inv_id_apply x).symm

/-! ### The comparison of Kähler differentials -/

/-- The map from the Kähler differentials of `φ` to those of the map induced on global sections
of the structure sheaves, induced by the square `ΓSpecIso_inv_comp_specAppLE`. -/
noncomputable def toSpecKaehler :
    CommRingCat.KaehlerDifferential φ ⟶
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
        (CommRingCat.KaehlerDifferential (specAppLE φ)) :=
  CommRingCat.KaehlerDifferential.map (ΓSpecIso_inv_comp_specAppLE φ)

/-- The map back, induced by the square `ΓSpecIso_hom_comp_self`. -/
noncomputable def fromSpecKaehler :
    CommRingCat.KaehlerDifferential (specAppLE φ) ⟶
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso A).hom.hom).obj
        (CommRingCat.KaehlerDifferential φ) :=
  CommRingCat.KaehlerDifferential.map (ΓSpecIso_hom_comp_self φ)

/-- The comparison carries the universal differential of `a : A` to the universal differential
of the corresponding global section of the structure sheaf. -/
theorem toSpecKaehler_d (a : A) :
    (toSpecKaehler φ).hom (CommRingCat.KaehlerDifferential.d a) =
      CommRingCat.KaehlerDifferential.d ((Scheme.ΓSpecIso A).inv a) :=
  CommRingCat.KaehlerDifferential.map_d _ a

/-- The comparison back carries the universal differential of a global section of the structure
sheaf to the universal differential of the corresponding element of `A`. -/
theorem fromSpecKaehler_d (b : Γ(Spec A, ⊤)) :
    (fromSpecKaehler φ).hom (CommRingCat.KaehlerDifferential.d b) =
      CommRingCat.KaehlerDifferential.d ((Scheme.ΓSpecIso A).hom b) :=
  CommRingCat.KaehlerDifferential.map_d _ b

/-- The composite of the two comparisons, as an endomorphism of the Kähler differentials of
`φ`: the two restrictions of scalars that the composite passes through cancel, and do not
change the underlying module. -/
private noncomputable def specKaehlerRoundTrip :
    CommRingCat.KaehlerDifferential φ ⟶ CommRingCat.KaehlerDifferential φ :=
  toSpecKaehler φ ≫
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).map (fromSpecKaehler φ) ≫
    (ModuleCat.restrictScalarsComp'App (Scheme.ΓSpecIso A).inv.hom (Scheme.ΓSpecIso A).hom.hom
      (RingHom.id A) (id_eq_ΓSpecIso_hom_comp_inv (A := A))
      (CommRingCat.KaehlerDifferential φ)).inv ≫
    (ModuleCat.restrictScalarsId'App (RingHom.id A) rfl
      (CommRingCat.KaehlerDifferential φ)).hom

/-- The composite of the two comparisons in the other order, as an endomorphism of the Kähler
differentials of the map induced on global sections of the structure sheaves. -/
private noncomputable def specKaehlerRoundTrip' :
    CommRingCat.KaehlerDifferential (specAppLE φ) ⟶
      CommRingCat.KaehlerDifferential (specAppLE φ) :=
  fromSpecKaehler φ ≫
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso A).hom.hom).map (toSpecKaehler φ) ≫
    (ModuleCat.restrictScalarsComp'App (Scheme.ΓSpecIso A).hom.hom (Scheme.ΓSpecIso A).inv.hom
      (RingHom.id Γ(Spec A, ⊤)) (id_eq_ΓSpecIso_inv_comp_hom (A := A))
      (CommRingCat.KaehlerDifferential (specAppLE φ))).inv ≫
    (ModuleCat.restrictScalarsId'App (RingHom.id Γ(Spec A, ⊤)) rfl
      (CommRingCat.KaehlerDifferential (specAppLE φ))).hom

private theorem specKaehlerRoundTrip_apply (x : CommRingCat.KaehlerDifferential φ) :
    (specKaehlerRoundTrip φ).hom x = (fromSpecKaehler φ).hom ((toSpecKaehler φ).hom x) :=
  rfl

private theorem specKaehlerRoundTrip'_apply
    (y : CommRingCat.KaehlerDifferential (specAppLE φ)) :
    (specKaehlerRoundTrip' φ).hom y = (toSpecKaehler φ).hom ((fromSpecKaehler φ).hom y) :=
  rfl

private theorem specKaehlerRoundTrip_eq_id : specKaehlerRoundTrip φ = 𝟙 _ := by
  refine CommRingCat.KaehlerDifferential.ext fun a => ?_
  simp only [specKaehlerRoundTrip_apply, toSpecKaehler_d, fromSpecKaehler_d,
    Iso.inv_hom_id_apply, ModuleCat.id_apply]

private theorem specKaehlerRoundTrip'_eq_id : specKaehlerRoundTrip' φ = 𝟙 _ := by
  refine CommRingCat.KaehlerDifferential.ext fun b => ?_
  simp only [specKaehlerRoundTrip'_apply, fromSpecKaehler_d, toSpecKaehler_d,
    Iso.hom_inv_id_apply, ModuleCat.id_apply]

/-- The comparison back is a left inverse of the comparison. -/
theorem fromSpecKaehler_toSpecKaehler (x : CommRingCat.KaehlerDifferential φ) :
    (fromSpecKaehler φ).hom ((toSpecKaehler φ).hom x) = x := by
  rw [← specKaehlerRoundTrip_apply, specKaehlerRoundTrip_eq_id]
  rfl

/-- The comparison back is a right inverse of the comparison. -/
theorem toSpecKaehler_fromSpecKaehler (y : CommRingCat.KaehlerDifferential (specAppLE φ)) :
    (toSpecKaehler φ).hom ((fromSpecKaehler φ).hom y) = y := by
  rw [← specKaehlerRoundTrip'_apply, specKaehlerRoundTrip'_eq_id]
  rfl

/-- **The Kähler differentials of `φ` and of the map it induces on global sections
of the structure sheaves agree.** -/
theorem isIso_toSpecKaehler : IsIso (toSpecKaehler φ) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y h => ?_, fun y => ⟨(fromSpecKaehler φ).hom y, ?_⟩⟩
  · rw [← fromSpecKaehler_toSpecKaehler φ x, ← fromSpecKaehler_toSpecKaehler φ y]
    exact congrArg (fromSpecKaehler φ).hom h
  · exact toSpecKaehler_fromSpecKaehler φ y

/-- The isomorphism between the Kähler differentials of `φ` and those of the map induced on
global sections of the structure sheaves, over `Γ(Spec A, ⊤)` with scalars restricted to `A`. -/
noncomputable def specKaehlerIso :
    CommRingCat.KaehlerDifferential φ ≅
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).obj
        (CommRingCat.KaehlerDifferential (specAppLE φ)) :=
  @asIso _ _ _ _ (toSpecKaehler φ) (isIso_toSpecKaehler φ)

/-! ### The comparison on sections and on sheaves -/

/-- The sections over `⊤` of the sheaf of relative differentials of `Spec φ` are the Kähler
differentials of the map induced on global sections of the structure sheaves; this is
[Stacks Project, Tag 01UT] for the pair of affine opens `⊤ ≤ (Spec φ) ⁻¹ᵁ ⊤`, in the form of
the explicit comparison map. -/
noncomputable def topSectionsIso :
    CommRingCat.KaehlerDifferential (specAppLE φ) ≅
      (Scheme.Hom.relativeDifferentials (Spec.map φ)).val.obj (.op ⊤) :=
  @asIso _ _ _ _ (AffineDifferentials.kaehlerToSections (Spec.map φ) ⊤ ⊤ le_top)
    (isIso_kaehlerToSections (Spec.map φ) (isAffineOpen_top _) le_top (isAffineOpen_top _))

/-- **Stacks Project, Tag 01UT, for a morphism of affine schemes.** The global differentials of
`Spec φ : Spec A ⟶ Spec R` are the Kähler differentials `Ω[A⁄R]`, as `A`-modules. -/
noncomputable def sectionsIso :
    CommRingCat.KaehlerDifferential φ ≅
      moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentials (Spec.map φ)) :=
  specKaehlerIso φ ≪≫
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso A).inv.hom).mapIso (topSectionsIso φ)

/-- **The comparison of global differentials is compatible with the universal derivations.** It
carries the universal differential of `a : A` to the universal relative differential of the
global section of `𝒪_{Spec A}` corresponding to `a`. -/
theorem sectionsIso_d (a : A) :
    (sectionsIso φ).hom.hom (CommRingCat.KaehlerDifferential.d a) =
      (Scheme.Hom.universalRelativeDerivation (Spec.map φ)).d ((Scheme.ΓSpecIso A).inv a) :=
  (congrArg (AffineDifferentials.kaehlerToSections (Spec.map φ) ⊤ ⊤ le_top).hom
      (toSpecKaehler_d φ a)).trans
    (AffineDifferentials.kaehlerToSections_d (Spec.map φ) ⊤ ⊤ le_top _)

/-- **Uniqueness of the comparison of global differentials.** There is exactly one isomorphism
of `A`-modules from `Ω[A⁄R]` to the global differentials of `Spec φ` compatible with the
universal derivations. -/
@[stacks 01UT "affine case in the coordinate rings: the global differentials of Spec φ are Ω[A⁄R]"]
theorem existsUnique_sectionsIso :
    ∃! e : CommRingCat.KaehlerDifferential φ ≅
        moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentials (Spec.map φ)),
      ∀ a : A, e.hom.hom (CommRingCat.KaehlerDifferential.d a) =
        (Scheme.Hom.universalRelativeDerivation (Spec.map φ)).d ((Scheme.ΓSpecIso A).inv a) := by
  refine ⟨sectionsIso φ, sectionsIso_d φ, fun e he => Iso.ext ?_⟩
  refine CommRingCat.KaehlerDifferential.ext fun a => ?_
  exact (he a).trans (sectionsIso_d φ a).symm

/-- **Stacks Project, Tag 01UT, as a comparison of sheaves on an affine scheme.** The sheaf of
relative differentials of `Spec φ : Spec A ⟶ Spec R` is the quasi-coherent sheaf associated to
the Kähler differentials `Ω[A⁄R]`. -/
@[ega "IV 16.3.1" "partial", ega "IV 16.3.7" "degree-one clause", sga "7 VI 5.1" "special case"]
noncomputable def tildeKaehlerIso :
    (tilde.functor A).obj (CommRingCat.KaehlerDifferential φ) ≅
      Scheme.Hom.relativeDifferentials (Spec.map φ) :=
  (tilde.functor A).mapIso (sectionsIso φ) ≪≫
    @AffineBaseChangeLocality.tildeΓIso A (Scheme.Hom.relativeDifferentials (Spec.map φ))
      (Scheme.Hom.isQuasicoherent_relativeDifferentials _)

/-- The comparison of sheaves is the comparison on global sections, pushed through the
associated-sheaf functor and followed by the counit of the adjunction between that functor and
global sections. -/
theorem tildeKaehlerIso_hom :
    (tildeKaehlerIso φ).hom =
      (tilde.functor A).map (sectionsIso φ).hom ≫
        Scheme.Modules.fromTildeΓNatTrans.app
          (Scheme.Hom.relativeDifferentials (Spec.map φ)) :=
  rfl

/-- **The comparison of sheaves induces the comparison of global differentials.** Read on
global sections and composed with the unit of the adjunction, the comparison of sheaves is
`sectionsIso`; since the associated-sheaf functor is fully faithful, this determines
`tildeKaehlerIso`. -/
theorem toTildeΓ_comp_map_tildeKaehlerIso :
    tilde.toTildeΓNatIso.hom.app (CommRingCat.KaehlerDifferential φ) ≫
        moduleSpecΓFunctor.map (tildeKaehlerIso φ).hom =
      (sectionsIso φ).hom := by
  rw [tildeKaehlerIso_hom, Functor.map_comp, ← Category.assoc,
    show tilde.toTildeΓNatIso.hom.app (CommRingCat.KaehlerDifferential φ) ≫
        moduleSpecΓFunctor.map ((tilde.functor A).map (sectionsIso φ).hom) =
        (sectionsIso φ).hom ≫
          tilde.toTildeΓNatIso.hom.app
            (moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentials (Spec.map φ))) from
      (tilde.toTildeΓNatIso.hom.naturality (sectionsIso φ).hom).symm,
    Category.assoc,
    show tilde.toTildeΓNatIso.hom.app
          (moduleSpecΓFunctor.obj (Scheme.Hom.relativeDifferentials (Spec.map φ))) ≫
        moduleSpecΓFunctor.map (Scheme.Modules.fromTildeΓNatTrans.app
          (Scheme.Hom.relativeDifferentials (Spec.map φ))) = 𝟙 _ from
      tilde.adjunction.right_triangle_components _]
  exact Category.comp_id _

/-- **Uniqueness of the comparison of sheaves.** There is exactly one isomorphism from the
quasi-coherent sheaf associated to `Ω[A⁄R]` to the sheaf of relative differentials of `Spec φ`
carrying the global section determined by the universal differential of `a : A` to the
universal relative differential of the global section of `𝒪_{Spec A}` corresponding to `a`. -/
@[stacks 01UT "affine case as a sheaf comparison: Ω_{Spec A/Spec R} is the sheaf of Ω[A⁄R]"]
theorem existsUnique_tildeKaehlerIso :
    ∃! e : (tilde.functor A).obj (CommRingCat.KaehlerDifferential φ) ≅
        Scheme.Hom.relativeDifferentials (Spec.map φ),
      ∀ a : A,
        (tilde.toTildeΓNatIso.hom.app (CommRingCat.KaehlerDifferential φ) ≫
            moduleSpecΓFunctor.map e.hom).hom (CommRingCat.KaehlerDifferential.d a) =
          (Scheme.Hom.universalRelativeDerivation (Spec.map φ)).d
            ((Scheme.ΓSpecIso A).inv a) := by
  refine ⟨tildeKaehlerIso φ, fun a => ?_, fun e he => Iso.ext ?_⟩
  · rw [toTildeΓ_comp_map_tildeKaehlerIso]
    exact sectionsIso_d φ a
  · refine (tilde.adjunction.homEquiv _ _).injective ?_
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    show tilde.toTildeΓNatIso.hom.app (CommRingCat.KaehlerDifferential φ) ≫
        moduleSpecΓFunctor.map e.hom =
      tilde.toTildeΓNatIso.hom.app (CommRingCat.KaehlerDifferential φ) ≫
        moduleSpecΓFunctor.map (tildeKaehlerIso φ).hom
    rw [toTildeΓ_comp_map_tildeKaehlerIso]
    exact congrArg Iso.hom
      ((existsUnique_sectionsIso φ).unique
        (y₁ := tilde.toTildeΓNatIso.app (CommRingCat.KaehlerDifferential φ) ≪≫
          moduleSpecΓFunctor.mapIso e) he (sectionsIso_d φ))

end SpecComparison

end Stacks.AlgebraicGeometry.AffineDifferentialsIso

end
