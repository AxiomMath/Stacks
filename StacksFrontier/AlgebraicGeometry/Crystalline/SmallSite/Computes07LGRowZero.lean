module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamTransport
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.Computes07LGDeRhamRows

/-!
# The row `b = 0` of [Stacks, Tag 07LG], from the identification of the carried data

`...SmallSite.computes07LG_of_connections_of_deRhamRows` leaves `hrow0`: the identification, in
cohomology, of the complex `M ⊗^∧_D Ω^*_D` built from the carried divided power ring `Dr`, the
carried graded family of forms `Om` and the pair `(M, ∇)` of [Stacks, Lemma 60.17.3, Tag 07JG]
with the completed de Rham complex `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}` of the cosimplicial degree zero.

**That identification does not follow from the parameters it was stated over, and this module is
what repairs that.**  Nothing in `...SmallSite.Reduction07JG` relates `Om` to the forms of the
envelope: its eleven inherited clauses and `levelSystem_isLevel` give only the `Om`-component of
`thickeningRingHom`, a semilinear map `Om 1 → Ω_{T_e}` into the differentials of a level, and no
clause makes it injective, surjective or a base change.  So `Om` may be replaced by `Om ⊕ Z` for
any family `Z` carrying the zero wedge and zero differential: every clause of the datum, the
Leibniz rule `hleib`, the exterior conditions `hext` and `hdx` and the finiteness of `ι` continue
to hold, while `M ⊗^∧_D Ω^*_D` acquires the extra summand `M ⊗̂_D Z^*` and with it extra
cohomology.  The complex of the cosimplicial degree zero is untouched by that replacement, so no
identification of the two can be proved; without an identification of `Om` with the forms of the
envelope, `hrow0` is not merely unproved but false for some admissible parameters.

The repair is to carry the identification, as the data it is:
`...SmallSite.DegreeZeroIdentification07LG` says that the ring, the graded forms, the module and
the connection of the carried data **are** those of the cosimplicial degree zero.  It is an
identification of the *input* of [Stacks, Tag 07LG] and not of its conclusion; it plays the role
`hleib`, `hext` and `hdx` already play, namely of pinning the carried family of forms down to the
divided power forms the tag is about, and it is the least that makes `hrow0` provable, since
`hrow0` compares the two complexes in **every** exterior degree while the `Om`-component of
`thickeningRingHom` speaks only of degree one.

Given it, `hrow0` is `Crystalline.CompletedDeRham.comparisonHomologyIso` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CompletedDeRhamTransport.lean`.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `DegreeZeroIdentification07LG` — **the identification of the carried data with the data of the
  cosimplicial degree zero**: the ring, the graded forms with their wedge product, their de Rham
  differential and the universal differential, the module of each crystal, and the connection.

## Main results

* `hrow0_of_degreeZeroIdentification` — **`hrow0`, proved** from that identification.
* `computes07LG_of_connections_of_deRhamRows_of_identification` — the reduction of
  [Stacks, Tag 07LG] of `...SmallSite.computes07LG_of_connections_of_deRhamRows` with `hrow0`
  replaced by the identification.

## What is and is not proved

**No tag attribute is placed here.**  [Stacks, Tag 07LG] is
`...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`.  What falls here, in the reduction with named
hypotheses, is `hrow0`. The connections of the cosimplicial degrees and the row homotopy
equivalence of [Stacks, Lemma 60.20.2, Tag 07LD] are untouched.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public noncomputable section

universe u uI

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicTopology Opposite Simplicial

namespace Crystalline

open DividedPowers

namespace GlobalCrystallineSituation.SmallSite

variable (S : GlobalCrystallineSituation.{u}) (A : Type u) [CommRing A]
  (Dr : DividedPowerRing.{u}) (g : A →+* Dr) (Om : ℕ → Type u) [∀ i, AddCommGroup (Om i)]
  [∀ i, Module (Dr : Type u) (Om i)] [Module (Dr : Type u)ᵐᵒᵖ (Om 1)]
  [IsCentralScalar (Dr : Type u) (Om 1)] (der : DividedPowerDerivation A Dr g (Om 1))
  {ι : Type uI} [Finite ι] (dx : ι → Om 1)
  (wedge : ∀ i, Om i →ₗ[(Dr : Type u)] Om 1 →ₗ[(Dr : Type u)] Om (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1))
  (hleib : CompletedDeRham.IsGradedLeibniz Dr Om wedge deRham
    (derivationFun A Dr g (Om 1) der))
  [IsAffine S.X] [IsAffine S.S.scheme] (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  (R : Reduction07JG S A Dr g (Om 1) der S.p dx hp)
  (h07IT : ∀ F : SheafOfModules.{u} (structureSheaf S),
    F.IsQuasicoherentOnSite → IsSheafCrystal F)

/-- **The carried data of [Stacks, Tag 07LG] is the data of the cosimplicial degree zero.**

The parameters `Dr`, `Om`, `wedge`, `deRham` and the pair `(M, ∇)` that
`...SmallSite.Computes07LG` is stated over are abstract; the tag speaks of the completed divided
power envelope `D`, its graded divided power forms `Ω^*_D`, and the module with connection
attached to the crystal there.  This structure is the identification of the one with the other,
at the cosimplicial degree zero of [Stacks, Proposition 60.20.1, Tag 07JN], which is where the
envelope `D` of the tag sits inside the double complex.

Each field is an identification of an *input* of the tag, never of its conclusion: the ring, the
forms in every exterior degree with their wedge product, their de Rham differential and the
universal differential `d : D → Ω¹`, the module of each crystal in quasi-coherent modules, and
the connection.  The forms and modules are identified by a semilinear map with a semilinear
inverse rather than by a bundled `≃ₛₗ`, so that no `RingHomInvPair` instance is needed.

Carrying it is what makes `hrow0` true: see the module documentation for the family of
parameters at which the identification fails and `hrow0` with it. -/
public structure Forms07LGIdentification where
  /-- **The carried divided power ring is the completed envelope of the cosimplicial degree
  zero.** -/
  ringEquiv : (Dr : Type u) ≃+* (wholeSpaceDPAlgebra hp).completedRing S.p 0
  /-- **The carried forms of each exterior degree are the divided power forms of that degree**,
  semilinearly over `ringEquiv`. -/
  formsMap : ∀ i : ℕ, Om i →ₛₗ[(ringEquiv : (Dr : Type u) →+*
    (wholeSpaceDPAlgebra hp).completedRing S.p 0)] (wholeSpaceDPAlgebra hp).forms S.p i 0
  /-- Its inverse, semilinear over the inverse ring isomorphism. -/
  formsInv : ∀ i : ℕ, (wholeSpaceDPAlgebra hp).forms S.p i 0 →ₛₗ[(ringEquiv.symm :
    (wholeSpaceDPAlgebra hp).completedRing S.p 0 →+* (Dr : Type u))] Om i
  /-- The inverse undoes the identification. -/
  formsInv_formsMap : ∀ (i : ℕ) (ω : Om i), formsInv i (formsMap i ω) = ω
  /-- The identification undoes its inverse. -/
  formsMap_formsInv : ∀ (i : ℕ) (ω : (wholeSpaceDPAlgebra hp).forms S.p i 0),
    formsMap i (formsInv i ω) = ω
  /-- The identification carries the carried wedge product to the wedge product of the divided
  power forms. -/
  formsMap_wedge : ∀ (i : ℕ) (ω : Om i) (eta : Om 1),
    formsMap (i + 1) (wedge i ω eta) =
      (wholeSpaceDPAlgebra hp).wedge S.p 0 i (formsMap i ω) (formsMap 1 eta)
  /-- The identification carries the carried de Rham differential to that of the divided power
  forms. -/
  formsMap_deRham : ∀ (i : ℕ) (ω : Om i),
    formsMap (i + 1) (deRham i ω) = (wholeSpaceDPAlgebra hp).deRham S.p 0 i (formsMap i ω)
  /-- The identification carries the carried divided power derivation to the universal
  differential of the envelope. -/
  formsMap_derivation : ∀ a : (Dr : Type u),
    formsMap 1 (derivationFun A Dr g (Om 1) der a) =
      (wholeSpaceDPAlgebra hp).differential S.p 0 (ringEquiv a)

/-- **The forms half of the identification from a graded additive isomorphism.**

This is the shape the library's identifications of completed divided power forms already come in:
`Crystalline.CompletedFormsDPIso` carries one additive isomorphism
`Ω^i_{D} ≃+ Ω^i_{D'}` per exterior degree together with its compatibility with the wedge product,
the de Rham differential and the universal differential, and
`Crystalline.completedFormsDPIso` builds one out of an isomorphism of divided power rings.  So
the field is discharged by a divided power isomorphism and does not have to be assembled from
semilinear maps by hand. -/
public def Forms07LGIdentification.ofAddEquiv
    (ringEquiv : (Dr : Type u) ≃+* (wholeSpaceDPAlgebra hp).completedRing S.p 0)
    (formsEquiv : ∀ i : ℕ, Om i ≃+ (wholeSpaceDPAlgebra hp).forms S.p i 0)
    (hsmul : ∀ (i : ℕ) (a : (Dr : Type u)) (ω : Om i),
      formsEquiv i (a • ω) = ringEquiv a • formsEquiv i ω)
    (hwedge : ∀ (i : ℕ) (ω : Om i) (eta : Om 1),
      formsEquiv (i + 1) (wedge i ω eta) =
        (wholeSpaceDPAlgebra hp).wedge S.p 0 i (formsEquiv i ω) (formsEquiv 1 eta))
    (hderham : ∀ (i : ℕ) (ω : Om i),
      formsEquiv (i + 1) (deRham i ω) =
        (wholeSpaceDPAlgebra hp).deRham S.p 0 i (formsEquiv i ω))
    (hder : ∀ a : (Dr : Type u),
      formsEquiv 1 (derivationFun A Dr g (Om 1) der a) =
        (wholeSpaceDPAlgebra hp).differential S.p 0 (ringEquiv a)) :
    Forms07LGIdentification S A Dr g Om der wedge deRham hp where
  ringEquiv := ringEquiv
  formsMap i :=
    { toFun := formsEquiv i
      map_add' := map_add (formsEquiv i)
      map_smul' := hsmul i }
  formsInv i :=
    { toFun := (formsEquiv i).symm
      map_add' := map_add (formsEquiv i).symm
      map_smul' := fun a ω => by
        refine (formsEquiv i).injective ?_
        rw [AddEquiv.apply_symm_apply, hsmul, AddEquiv.apply_symm_apply]
        simp }
  formsInv_formsMap i ω := (formsEquiv i).symm_apply_apply ω
  formsMap_formsInv i ω := (formsEquiv i).apply_symm_apply ω
  formsMap_wedge := hwedge
  formsMap_deRham := hderham
  formsMap_derivation := hder

/-- **The field `ringEquiv` of the forms identification is inhabited at the divided power ring the
construction of [Stacks, Lemma 60.17.3, Tag 07JG] produces.**

`...SmallSite.reduction07JGWholeSpaceOfItems` builds a reduction datum over the divided power ring
`(wholeSpaceSystemEnvelope hp 0).ring`, the ring of the object `D(0)` the system of
[Stacks, Proposition 60.20.1, Tag 07JN] is built from.  The identification asks for a ring
isomorphism of the carried `Dr` with the completed envelope `D̂(0)` of the cosimplicial degree
zero, and at that `Dr` the isomorphism is
`...SmallSite.wholeSpaceSystemEnvelopeRingEquiv` — the two realisations of `D(0)` already
identified in the library.  So the ring field of the identification costs the construction of the
reduction datum nothing. -/
public def forms07LGIdentification_ringEquiv_wholeSpaceEnvelope :
    ((wholeSpaceSystemEnvelope hp 0).ring : Type u) ≃+*
      (wholeSpaceDPAlgebra hp).completedRing S.p 0 :=
  wholeSpaceSystemEnvelopeRingEquiv hp 0

/-- **The carried data of [Stacks, Tag 07LG] is the data of the cosimplicial degree zero**, forms
and module and connection.

`...SmallSite.Forms07LGIdentification` identifies the ring and the graded forms; this adds the
identification of the module of the pair attached to each crystal in quasi-coherent modules with
the module `M(0)` of [Stacks, Proposition 60.20.1, Tag 07JN] and of the connection of the pair
with the connection of the cosimplicial degree zero.

The two halves are separate because the forms half mentions neither the reduction datum nor the
coefficient sheaf, so it is the half an instantiation of `Om` at the genuine divided power forms
discharges on its own; see `...SmallSite.forms07LGIdentification_ringEquiv_wholeSpaceEnvelope`. -/
public structure DegreeZeroIdentification07LG
    (nabla0 : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      CompletedConnection S.p ((wholeSpaceDPAlgebra hp).completedRing S.p 0)
        ((wholeSpaceDPAlgebra hp).forms S.p 1 0) ((wholeSpaceDPAlgebra hp).differential S.p 0)
        ((wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier 0))
    extends Forms07LGIdentification S A Dr g Om der wedge deRham hp where
  /-- **The module of the pair attached to a crystal is the module `M(0)` of
  [Stacks, Proposition 60.20.1, Tag 07JN]**, semilinearly over `ringEquiv`. -/
  moduleMap : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
    ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier →ₛₗ[(ringEquiv :
      (Dr : Type u) →+* (wholeSpaceDPAlgebra hp).completedRing S.p 0)]
      (wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier 0
  /-- Its inverse, semilinear over the inverse ring isomorphism. -/
  moduleInv : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
    (wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier 0 →ₛₗ[
      (ringEquiv.symm : (wholeSpaceDPAlgebra hp).completedRing S.p 0 →+* (Dr : Type u))]
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier
  /-- The inverse undoes the identification. -/
  moduleInv_moduleMap : ∀ (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite)
    (m : ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier),
    moduleInv F hF (moduleMap F hF m) = m
  /-- The identification undoes its inverse. -/
  moduleMap_moduleInv : ∀ (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite)
    (m : (wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier 0),
    moduleMap F hF (moduleInv F hF m) = m
  /-- **The connection of the pair is the connection of the cosimplicial degree zero**, read
  through the identification of the modules and of the one-forms. -/
  moduleMap_nabla : ∀ (F : SheafOfModules.{u} (structureSheaf S))
    (hF : F.IsQuasicoherentOnSite)
    (m : ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier),
    nabla0 F hF (moduleMap F hF m) =
      CompletedDeRham.isoValuesFwd S.p ringEquiv (moduleMap F hF) formsMap 1
        (((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).nabla m)

/-- **The connection field of the identification is never an obstruction**: given the forms half
and the identification of the modules, the connection of the cosimplicial degree zero may be
*taken* to be the transport of the connection of the pair, and then `moduleMap_nabla` holds by
construction.

So the content of `...SmallSite.DegreeZeroIdentification07LG` is its forms half together with the
identification of the modules; nothing further about the connections is assumed, and the
structure is inhabited as soon as those are.  `Crystalline.CompletedDeRham.transportConnection`
is a genuine completed connection — its Leibniz rule is proved, using the field
`formsMap_derivation` of the forms half — so this is not a reparametrisation of the hypothesis. -/
public def DegreeZeroIdentification07LG.ofModuleIdentification
    (I : Forms07LGIdentification S A Dr g Om der wedge deRham hp)
    (moduleMap : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier →ₛₗ[(I.ringEquiv :
        (Dr : Type u) →+* (wholeSpaceDPAlgebra hp).completedRing S.p 0)]
        (wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier 0)
    (moduleInv : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      (wholeSpaceCosimplicialModule hp
        (toQuasiCoherentCrystal S h07IT F hF)).carrier 0 →ₛₗ[(I.ringEquiv.symm :
          (wholeSpaceDPAlgebra hp).completedRing S.p 0 →+* (Dr : Type u))]
        ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier)
    (hleft : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (m : ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).carrier),
      moduleInv F hF (moduleMap F hF m) = m)
    (hright : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (m : (wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier 0),
      moduleMap F hF (moduleInv F hF m) = m) :
    DegreeZeroIdentification07LG S A Dr g Om der dx wedge deRham hp R h07IT
      (fun F hF => CompletedDeRham.transportConnection S.p I.ringEquiv (moduleMap F hF)
        (moduleInv F hF) I.formsMap (derivationFun A Dr g (Om 1) der)
        ((wholeSpaceDPAlgebra hp).differential S.p 0)
        ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).nabla (hright F hF)
        I.formsMap_derivation) where
  toForms07LGIdentification := I
  moduleMap := moduleMap
  moduleInv := moduleInv
  moduleInv_moduleMap := hleft
  moduleMap_moduleInv := hright
  moduleMap_nabla F hF m :=
    CompletedDeRham.transportConnection_apply S.p I.ringEquiv (moduleMap F hF) (moduleInv F hF)
      I.formsMap (derivationFun A Dr g (Om 1) der)
      ((wholeSpaceDPAlgebra hp).differential S.p 0)
      ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).nabla (hleft F hF) (hright F hF)
      I.formsMap_derivation m

/-- **The hypothesis `hrow0` of [Stacks, Proposition 60.21.3, Tag 07LG], proved** from the
identification of the carried data with the data of the cosimplicial degree zero.

The two complexes are `Crystalline.CompletedDeRham.complex` at data that the identification makes
isomorphic piece by piece, so
`Crystalline.CompletedDeRham.comparisonHomologyIso` identifies their cohomology in every
degree. -/
public theorem hrow0_of_degreeZeroIdentification
    (hext : CompletedDeRham.IsGradedExterior (Dr : Type u) Om wedge deRham)
    (hdx : ∀ j, deRham 1 (dx j) = 0)
    (nabla : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (b : ℕ), CompletedConnection S.p ((wholeSpaceDPAlgebra hp).completedRing S.p b)
        ((wholeSpaceDPAlgebra hp).forms S.p 1 b) ((wholeSpaceDPAlgebra hp).differential S.p b)
        ((wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier b))
    (hnabla : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      {m n : SimplexCategory} (φ : m ⟶ n)
      (x : (wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier m.len),
      nabla F hF n.len
          ((wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).map φ x) =
        (wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).tensorMap φ 1
          (nabla F hF m.len x))
    (hsqz : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (b : ℕ),
      CompletedDeRham.IsSquareZero S.p ((wholeSpaceDPAlgebra hp).completedRing S.p b)
        (fun a => (wholeSpaceDPAlgebra hp).forms S.p a b) ((wholeSpaceDPAlgebra hp).wedge S.p b)
        ((wholeSpaceDPAlgebra hp).deRham S.p b)
        ((wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier b)
        (nabla F hF b) ((wholeSpaceDPAlgebra hp).isGradedLeibniz S.p b))
    (I : DegreeZeroIdentification07LG S A Dr g Om der dx wedge deRham hp R h07IT
      (fun F hF => nabla F hF 0))
    (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (j : ℕ) :
    Nonempty
      ((crystalDeRhamComplex S A Dr g Om der S.p dx wedge deRham hleib R h07IT F hF
          (squareZero07JG S A Dr g Om der S.p dx wedge deRham hleib hp R h07IT hext hdx
            F hF)).homology j ≅
        ((wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).degreeDeRhamComplex 0).homology j) :=
  ⟨CompletedDeRham.comparisonHomologyIso S.p I.ringEquiv (I.moduleMap F hF) (I.moduleInv F hF)
    I.formsMap I.formsInv (I.moduleInv_moduleMap F hF) (I.moduleMap_moduleInv F hF)
    I.formsInv_formsMap I.formsMap_formsInv wedge ((wholeSpaceDPAlgebra hp).wedge S.p 0)
    deRham ((wholeSpaceDPAlgebra hp).deRham S.p 0)
    ((functor07JG R).obj (toQuasiCoherentCrystal S h07IT F hF)).nabla (nabla F hF 0)
    hleib ((wholeSpaceDPAlgebra hp).isGradedLeibniz S.p 0)
    I.formsMap_wedge I.formsMap_deRham (I.moduleMap_nabla F hF)
    (squareZero07JG S A Dr g Om der S.p dx wedge deRham hleib hp R h07IT hext hdx F hF)
    (hsqz F hF 0) j⟩

/-- **[Stacks, Proposition 60.21.3, Tag 07LG] from the per-degree connections, the completed de
Rham form of the rows, and the identification of the carried data.**

This is `...SmallSite.computes07LG_of_connections_of_deRhamRows` with its hypothesis `hrow0`
discharged: the identification of the ring, the forms, the module and the connection with those
of the cosimplicial degree zero replaces it, and that identification is input data of the tag, as
`hleib`, `hext` and `hdx` are, rather than any part of its conclusion.

Nothing is weakened: the conclusion is `...SmallSite.Computes07LG`. -/
public theorem computes07LG_of_connections_of_deRhamRows_of_identification
    (hext : CompletedDeRham.IsGradedExterior (Dr : Type u) Om wedge deRham)
    (hdx : ∀ j, deRham 1 (dx j) = 0)
    (nabla : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      (b : ℕ), CompletedConnection S.p ((wholeSpaceDPAlgebra hp).completedRing S.p b)
        ((wholeSpaceDPAlgebra hp).forms S.p 1 b) ((wholeSpaceDPAlgebra hp).differential S.p b)
        ((wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier b))
    (hnabla : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite)
      {m n : SimplexCategory} (φ : m ⟶ n)
      (x : (wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier m.len),
      nabla F hF n.len
          ((wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).map φ x) =
        (wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).tensorMap φ 1
          (nabla F hF m.len x))
    (hsqz : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite) (b : ℕ),
      CompletedDeRham.IsSquareZero S.p ((wholeSpaceDPAlgebra hp).completedRing S.p b)
        (fun a => (wholeSpaceDPAlgebra hp).forms S.p a b) ((wholeSpaceDPAlgebra hp).wedge S.p b)
        ((wholeSpaceDPAlgebra hp).deRham S.p b)
        ((wholeSpaceCosimplicialModule hp (toQuasiCoherentCrystal S h07IT F hF)).carrier b)
        (nabla F hF b) ((wholeSpaceDPAlgebra hp).isGradedLeibniz S.p b))
    (N : ∀ (F : SheafOfModules.{u} (structureSheaf S)), F.IsQuasicoherentOnSite → ℕ → Type u)
    [instN : ∀ F hF i, AddCommGroup (N F hF i)]
    (dL : ∀ F hF i, N F hF i →+ N F hF (i + 1))
    (hdL : ∀ F hF (i : ℕ) (x : N F hF i), dL F hF (i + 1) (dL F hF i x) = 0)
    (rho : ∀ (F : SheafOfModules.{u} (structureSheaf S)) (hF : F.IsQuasicoherentOnSite),
      wholeSpaceDoubleComplex hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF) ⟶
        AlgebraicTopology.constantCosimplicialCochainComplex.obj
          (deRhamComparisonTarget (N F hF) (dL F hF) (hdL F hF)))
    (iotaDeg : ∀ F hF (b i : ℕ), N F hF i →+
      (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
        (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj i b)
    (piDeg : ∀ F hF (b i : ℕ),
      (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
        (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj i b →+ N F hF i)
    (hDeg : ∀ F hF (b i : ℕ),
      (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj (i + 1) b →+
        (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj i b)
    (hiota : ∀ F hF (b i : ℕ) (x : N F hF i),
      (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).degreeDifferential b i (iotaDeg F hF b i x) =
        iotaDeg F hF b (i + 1) (dL F hF i x))
    (hpi : ∀ F hF (b i : ℕ) (y :
        (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj i b),
      dL F hF i (piDeg F hF b i y) = piDeg F hF b (i + 1)
        ((wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).degreeDifferential b i y))
    (hretract : ∀ F hF (b i : ℕ) (x : N F hF i), piDeg F hF b i (iotaDeg F hF b i x) = x)
    (h0 : ∀ F hF (b : ℕ) (x :
        (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj 0 b),
      hDeg F hF b 0
          ((wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
            (hnabla F hF) (hsqz F hF)).degreeDifferential b 0 x) +
        iotaDeg F hF b 0 (piDeg F hF b 0 x) = x)
    (hsucc : ∀ F hF (b i : ℕ) (x :
        (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).toCosimplicialCompletedModule.obj (i + 1) b),
      (wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
            (hnabla F hF) (hsqz F hF)).degreeDifferential b i (hDeg F hF b i x) +
          hDeg F hF b (i + 1)
            ((wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
              (hnabla F hF) (hsqz F hF)).degreeDifferential b (i + 1) x) +
          iotaDeg F hF b (i + 1) (piDeg F hF b (i + 1) x) = x)
    (hsec : ∀ F hF (b i : ℕ) (x : N F hF i),
      ((wholeSpaceCosimplicialPair hp (toQuasiCoherentCrystal S h07IT F hF) (nabla F hF)
          (hnabla F hF) (hsqz F hF)).rowDeRhamComparison (rho F hF) b).f i
        (iotaDeg F hF b i x) = x)
    (I : DegreeZeroIdentification07LG S A Dr g Om der dx wedge deRham hp R h07IT
      (fun F hF => nabla F hF 0)) :
    Computes07LG S A Dr g Om der S.p dx wedge deRham hleib hp R h07IT
      (squareZero07JG S A Dr g Om der S.p dx wedge deRham hleib hp R h07IT hext hdx) :=
  computes07LG_of_connections_of_deRhamRows S A Dr g Om der S.p dx wedge deRham hleib hp R h07IT
    hext hdx nabla hnabla hsqz N dL hdL rho iotaDeg piDeg hDeg hiota hpi hretract h0 hsucc hsec
    (fun F hF j => hrow0_of_degreeZeroIdentification S A Dr g Om der dx wedge deRham hleib hp R
      h07IT hext hdx nabla hnabla hsqz I F hF j)

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
