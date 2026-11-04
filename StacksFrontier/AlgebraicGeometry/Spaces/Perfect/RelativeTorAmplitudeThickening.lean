module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectThickening
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingComplexGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeGeometricStalks
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleNeighborhoodBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversalThickeningUnramified
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutLegFiniteOrder

/-!
# Relative Tor amplitude ascends along a finite-order thickening of the base, at the stalks

Consider a cartesian square of algebraic spaces
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
with `f` flat and `g` a finite-order thickening.  This file proves the stalkwise content of the
Tor half of Stacks 0DL4: at a geometric point `x̄'` of `X'`, a Tor-amplitude bound over
`𝒪_{Y', ȳ'}` for `K ⊗_{𝒪_{X, x̄}} 𝒪_{X', x̄'}` gives the same bound over `𝒪_{Y, ȳ}` for a K-flat
complex `K` of `𝒪_{X, x̄}`-modules.  It also proves that the stalk maps of a finite-order
thickening are surjective with nilpotent kernel, which is what the transfer needs.

## Main results

* `AlgebraicGeometry.Space.isPushout_of_flat_of_surjective`: a flat local quotient of a pushout
  of rings along a surjection is the pushout.
* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_of_extendScalars_of_isNilpotent`: the
  Tor-amplitude half of Stacks 0DJG for a K-flat complex, read on the termwise extension of
  scalars.
* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_geometricStalk_of_baseChange_of_isNilpotent`:
  the transfer at a geometric point.
* `AlgebraicGeometry.Space.ker_smallEtaleStalkPullbackRingMap_pow_eq_bot` and
  `AlgebraicGeometry.Space.surjective_and_isNilpotent_ker_stalkStructureMap`: the stalk maps of a
  morphism whose base changes to schemes are `n`th-order thickenings are surjective, with kernel of
  vanishing `(n + 1)`st power.

## Implementation notes

A finite-order thickening `g` is given as a morphism every base change of which to a scheme is an
`n`th-order thickening of schemes, `(thickOrder n).inverseImage toScheme` read through
`CategoryTheory.MorphismProperty.presheaf`, the convention by which this library reads every
property of morphisms of algebraic spaces off representable base changes (closed immersions,
Stacks 02YU).  That is the form in which the order of the thickening reaches the regular functions
on étale charts, where the nilpotence of the kernel of a stalk map is computed.

Nothing here uses Stacks 0DKQ: the transfer is made directly at the geometric stalks, where the
square of stalk rings is a pushout along a surjection with nilpotent kernel.

## References

* [Stacks Project, Tag 0DL4](https://stacks.math.columbia.edu/tag/0DL4)
* [Stacks Project, Tag 0DJG](https://stacks.math.columbia.edu/tag/0DJG)
* [Stacks Project, Tag 0H75](https://stacks.math.columbia.edu/tag/0H75)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.TorAmplitude
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

section RingLevel

-- The standard model is forced:
-- `Stacks.Thickenings.hasTorAmplitudeCanonical_of_derivedExtensionScalars` and
-- `HasTorAmplitudeCanonical` are stated only for it, and a plain-priority pin loses to the global
-- instances on `ModuleCat`.
attribute [local instance 10000] HasDerivedCategory.standard

/-- **A flat local quotient of a pushout is the pushout.** Let `R → A` and `R → B` be ring maps
with `R → B` surjective, `A` local, and let `φ : A ⊗_R B → C` be a flat ring map to a local ring
`C` whose restriction to `A` is a surjective local homomorphism. Then `φ` is bijective, so `C` is
the pushout `A ⊗_R B`.

`A ⊗_R B` is a quotient of `A`, hence local, and `φ` is local because its restriction to `A` is;
a flat local homomorphism of local rings is faithfully flat, hence injective, and it is
surjective because its restriction to `A` is. -/
theorem isPushout_of_flat_of_surjective {R A B C : Type u} [CommRing R] [CommRing A]
    [CommRing B] [CommRing C] [Algebra R A] [Algebra R B] [Algebra A C] [Algebra B C]
    [Algebra R C] [IsScalarTower R A C] [IsScalarTower R B C] [IsLocalRing A] [IsLocalRing C]
    [IsLocalHom (algebraMap A C)]
    (hB : Function.Surjective (algebraMap R B)) (hC : Function.Surjective (algebraMap A C))
    (φ : A ⊗[R] B →+* C) (hl : φ.comp Algebra.TensorProduct.includeLeftRingHom = algebraMap A C)
    (hr : φ.comp Algebra.TensorProduct.includeRight.toRingHom = algebraMap B C)
    (hflat : φ.Flat) :
    Algebra.IsPushout R A B C := by
  have hincl : Function.Surjective (Algebra.TensorProduct.includeLeftRingHom :
      A →+* A ⊗[R] B) :=
    Algebra.TensorProduct.includeLeft_surjective (R := R) (T := B) R A hB
  have : Nontrivial (A ⊗[R] B) := φ.domain_nontrivial
  have : IsLocalRing (A ⊗[R] B) := IsLocalRing.of_surjective' _ hincl
  let := φ.toAlgebra
  have : Module.Flat (A ⊗[R] B) C := RingHom.flat_algebraMap_iff.mp hflat
  have : IsLocalHom (algebraMap (A ⊗[R] B) C) := by
    refine ⟨fun t ht => ?_⟩
    obtain ⟨a, rfl⟩ := hincl t
    have ha : IsUnit (algebraMap A C a) := by
      rw [← hl]
      exact ht
    exact (isUnit_of_map_unit (algebraMap A C) a ha).map _
  have : Module.FaithfullyFlat (A ⊗[R] B) C := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective φ := FaithfulSMul.algebraMap_injective (A ⊗[R] B) C
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨a, rfl⟩ := hC c
    exact ⟨Algebra.TensorProduct.includeLeftRingHom a, by rw [← hl]; rfl⟩
  let : Algebra B (A ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R B (A ⊗[R] B) := Algebra.TensorProduct.right_isScalarTower
  let φA : A ⊗[R] B →ₐ[A] C :=
    { φ with commutes' := fun a => DFunLike.congr_fun hl a }
  let e : A ⊗[R] B ≃ₐ[A] C := AlgEquiv.ofBijective φA ⟨hinj, hsurj⟩
  exact Algebra.IsPushout.of_equiv (R := R) (R' := A) (S := B) (S' := A ⊗[R] B) e
    (by ext b; exact DFunLike.congr_fun hr b)

/-- **Tor amplitude ascends along a nilpotent thickening of the base, for a K-flat complex.**
Let `R' → R` be surjective with nilpotent kernel, let `A'` be a flat `R'`-algebra and let `A` be
the base change `A' ⊗_{R'} R`, presented as a pushout square. If `K` is a K-flat complex of
`A'`-modules and `K ⊗_{A'} A`, read over `R`, has Tor amplitude in `[a, b]`, then `K`, read over
`R'`, has Tor amplitude in `[a, b]`.

This is the Tor-amplitude half of Stacks 0DJG
(`Stacks.Thickenings.hasTorAmplitudeCanonical_of_derivedExtensionScalars`), with the derived
extension of scalars of the K-flat complex `K` computed termwise. -/
theorem hasTorAmplitudeCanonical_of_extendScalars_of_isNilpotent
    {R' A' R A : Type u} [CommRing R'] [CommRing A'] [CommRing R] [CommRing A]
    [Algebra R' A'] [Algebra R' R] [Algebra R' A] [Algebra A' A] [Algebra R A]
    [IsScalarTower R' A' A] [IsScalarTower R' R A] [Algebra.IsPushout R' A' R A]
    [Module.Flat R' A']
    (hsurj : Function.Surjective (algebraMap R' R))
    (hnil : IsNilpotent (RingHom.ker (algebraMap R' R)))
    (K : CochainComplex (ModuleCat.{u} A') ℤ) (hK : K.KFlat) (a b : ℤ)
    (h : HasTorAmplitudeCanonical R
      (DerivedCategory.Q.obj
        (((ModuleCat.restrictScalars (algebraMap R A)).mapHomologicalComplex (.up ℤ)).obj
          (((ModuleCat.extendScalars (algebraMap A' A)).mapHomologicalComplex (.up ℤ)).obj K)))
      a b) :
    HasTorAmplitudeCanonical R'
      ((ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)) a b := by
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A' A)
  have : IsIso (D.comparison.app K) := D.comparison_isIso_of_kFlat K hK
  refine Stacks.Thickenings.hasTorAmplitudeCanonical_of_derivedExtensionScalars hsurj hnil
    (DerivedCategory.Q.obj K) _ (asIso (D.comparison.app K)) a b ?_
  exact AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.app _).symm a b h

end RingLevel

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Precomposing with a ring isomorphism keeps a homomorphism surjective with nilpotent kernel. -/
theorem surjective_and_isNilpotent_ker_comp_ringEquiv {A B' C : Type*} [CommRing A] [CommRing B']
    [CommRing C] (e : A ≃+* B') (φ : B' →+* C) (hs : Function.Surjective φ)
    (hn : IsNilpotent (RingHom.ker φ)) :
    Function.Surjective (φ.comp e.toRingHom) ∧ IsNilpotent (RingHom.ker (φ.comp e.toRingHom)) := by
  refine ⟨hs.comp e.surjective, ?_⟩
  have hker : RingHom.ker (φ.comp e.toRingHom) = Ideal.map e.symm.toRingHom (RingHom.ker φ) := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective e.symm.toRingHom e.symm.surjective]
    constructor
    · intro ha
      exact ⟨e a, ha, e.symm_apply_apply a⟩
    · rintro ⟨b, hb, rfl⟩
      show φ (e (e.symm b)) = 0
      rw [e.apply_symm_apply]
      exact hb
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, ?_⟩
  rw [hker, Ideal.zero_eq_bot, ← Ideal.map_pow]
  rw [Ideal.zero_eq_bot] at hn
  rw [hn, Ideal.map_bot]

section Stalks

-- The standard model is forced: `HasTorAmplitudeCanonical` is stated only for it, and a
-- plain-priority pin loses to the global instances on `ModuleCat`.
attribute [local instance 10000] HasDerivedCategory.standard

open AlgebraicGeometry.BaseChangeTorAmplitude in
/-- **Relative Tor amplitude ascends along a thickening of the base, at a geometric point.**
Consider a cartesian square of algebraic spaces
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
with `f` flat and `g'` a closed immersion, and a geometric point `x̄'` of `X'` at whose image
`ȳ'` in `Y'` the fibre `𝒪_{Y, ȳ} ⟶ 𝒪_{Y', ȳ'}` of the structure map of `g` is surjective with
nilpotent kernel.  If `K` is a K-flat complex of `𝒪_{X, x̄}`-modules and
`K ⊗_{𝒪_{X, x̄}} 𝒪_{X', x̄'}` has Tor amplitude in `[a, b]` over `𝒪_{Y', ȳ'}`, then `K` has Tor
amplitude in `[a, b]` over `𝒪_{Y, ȳ}`.

The square of geometric stalks is a pushout: `𝒪_{X', x̄'}` is flat over `𝒪_{X, x̄} ⊗ 𝒪_{Y', ȳ'}`
(`AlgebraicGeometry.Space.cartesian_geometricStalk_tensor_flat`), a quotient of `𝒪_{X, x̄}`
because `g'` is a closed immersion, and a flat surjection of local rings is bijective
(`AlgebraicGeometry.Space.isPushout_of_flat_of_surjective`).  The transfer is then the nilpotent
dévissage of Stacks 0H75 in the form of
`AlgebraicGeometry.Space.hasTorAmplitudeCanonical_of_extendScalars_of_isNilpotent`. -/
theorem hasTorAmplitudeCanonical_geometricStalk_of_baseChange_of_isNilpotent
    {X' X Y' Y : AlgebraicSpaces B S hS}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (hpb : IsPullback g' f' f g)
    (hf : IsFlat B S hS f.hom) (hg' : IsClosedImmersion B S hS g'.hom)
    (x' : GeometricPoint B S hS X'.1)
    (hsurj : Function.Surjective (stalkStructureMap B S hS g (geometricPointMap f'.hom x')).hom)
    (hnil : IsNilpotent (RingHom.ker
      (stalkStructureMap B S hS g (geometricPointMap f'.hom x')).hom))
    (K : CochainComplex
      (ModuleCat.{u} (geometricStalkRing B S hS (geometricPointMap g'.hom x'))) ℤ)
    (hK : CochainComplex.KFlat.{u, u} K) (a b : ℤ)
    (h : HasTorAmplitudeCanonical (geometricStalkRing B S hS (geometricPointMap f'.hom x'))
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars
        (stalkStructureMap B S hS f' x').hom).obj
        ((CochainComplex.extendScalars (stalkStructureMap B S hS g' x').hom).obj K))) a b) :
    HasTorAmplitudeCanonical
      (geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x')))
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars
        (stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom).obj K)) a b := by
  let R := geometricStalkRing B S hS (geometricPointMap f.hom (geometricPointMap g'.hom x'))
  let A := geometricStalkRing B S hS (geometricPointMap g'.hom x')
  let B' := geometricStalkRing B S hS (geometricPointMap f'.hom x')
  let C := geometricStalkRing B S hS x'
  let : Algebra R A := (stalkStructureMap B S hS f (geometricPointMap g'.hom x')).hom.toAlgebra
  let : Algebra R B' := (geometricBaseStalkMap B S hS f g f' g' hpb.w x').hom.toAlgebra
  obtain ⟨φ, hleft, hright, hflat⟩ := cartesian_geometricStalk_tensor_flat B S hS g' f' f g hpb x'
  let : Algebra A C := (stalkStructureMap B S hS g' x').hom.toAlgebra
  let : Algebra B' C := (stalkStructureMap B S hS f' x').hom.toAlgebra
  let : Algebra R C := ((algebraMap A C).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq' rfl
  have hsq : (algebraMap A C).comp (algebraMap R A) = (algebraMap B' C).comp (algebraMap R B') := by
    show (stalkStructureMap B S hS g' x').hom.comp (algebraMap R A) =
      (stalkStructureMap B S hS f' x').hom.comp (algebraMap R B')
    rw [← hleft, ← hright, RingHom.comp_assoc, RingHom.comp_assoc,
      Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap]
  have : IsScalarTower R B' C := IsScalarTower.of_algebraMap_eq' hsq
  have : Module.Flat R A :=
    flat_stalkStructureMap B S hS f (geometricPointMap g'.hom x') hf
  have : IsLocalRing A := isLocalRing_geometricStalkRing B S hS X _
  have : IsLocalRing C := isLocalRing_geometricStalkRing B S hS X' x'
  have : IsLocalHom (algebraMap A C) := isLocalHom_stalkStructureMap B S hS g' x'
  let eR :
      R ≃+* geometricStalkRing B S hS (geometricPointMap g.hom (geometricPointMap f'.hom x')) :=
    (eqToIso (congrArg (fun z : GeometricPoint B S hS Y.1 => geometricStalkRing B S hS (X := Y) z)
      (geometricPointMap_square B S hS f g f' g' hpb.w x'))).commRingCatIsoToRingEquiv
  obtain ⟨hsR, hnR⟩ := surjective_and_isNilpotent_ker_comp_ringEquiv eR _ hsurj hnil
  have hsurjA : Function.Surjective (algebraMap A C) := by
    show Function.Surjective (stalkStructureMap B S hS g' x').hom
    rw [stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap]
    exact surjective_smallEtaleStalkPullbackRingMap_of_isClosedImmersion B S hS g' x' hg'
  have : Algebra.IsPushout R A B' C :=
    isPushout_of_flat_of_surjective hsR hsurjA φ hleft hright hflat
  exact hasTorAmplitudeCanonical_of_iso
    ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategoryFactors.app K)
    a b (hasTorAmplitudeCanonical_of_extendScalars_of_isNilpotent (R' := R) (A' := A) (R := B')
      (A := C) hsR hnR K hK a b h)

end Stalks

section Nilpotent

open CategoryTheory.GrothendieckTopology Opposite

variable {V U : AlgebraicSpaces B S hS}

/-- Pulling a regular function on an étale chart of `U` back to the base change along a
representable `h : V ⟶ U` commutes with restriction along a morphism of charts. -/
theorem structurePresheaf_map_snd (h : V ⟶ U) (hh : yoneda.relativelyRepresentable h.hom)
    {W W' : SmallEtale B S hS U.1} (g : W' ⟶ W) (s : (structurePresheaf B S hS U.1).obj (op W)) :
    (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (hh.snd W'.1.hom))))
        ((structurePresheaf B S hS U.1).map g.op s) =
      ((structurePresheaf B S hS V.1).map ((smallBaseChange B S hS h hh).map g).op)
        (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (hh.snd W.1.hom))) s) := by
  have key : (BigFppfOver.toScheme B S hS).map ((smallBaseChange B S hS h hh).map
        g).hom.left ≫ (BigFppfOver.toScheme B S hS).map (hh.snd W.1.hom) =
      (BigFppfOver.toScheme B S hS).map (hh.snd W'.1.hom) ≫
        (BigFppfOver.toScheme B S hS).map g.hom.left :=
    ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
      ((congrArg (fun m => (BigFppfOver.toScheme B S hS).map m)
        (smallBaseChange_map_snd B S hS h hh g)).trans
        ((BigFppfOver.toScheme B S hS).map_comp _ _))
  show (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map g.hom.left)) ≫
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (hh.snd W'.1.hom)))) s =
    (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (hh.snd W.1.hom))) ≫
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map
        ((smallBaseChange B S hS h hh).map g).hom.left))) s
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg (fun m => (Scheme.Γ.map m) s) (congrArg Quiver.Hom.op key.symm)

/-- **The kernel of the stalk map of a closed immersion is made of germs killed on a base
change.**  Let `h : V ⟶ U` be a closed immersion of algebraic spaces and `ȳ` a geometric point of
`V`.  Every element of the kernel of `(𝒪_U)_{h(ȳ)} ⟶ (𝒪_V)_{ȳ}` is the germ, on a pointed étale
chart `W` of `U`, of a regular function whose pullback to `V ×_U W` vanishes.

A germ killed by the stalk map vanishes on a pointed chart of `V` refining `V ×_U W`; that chart
is refined by a base-changed one, and the morphism between base changes is, after a further
refinement, the base change of a morphism of pointed charts of `U`
(`AlgebraicGeometry.Space.SmallEtaleNeighborhood.exists_baseChange_factorization`), along which
the function is restricted. -/
theorem exists_germ_eq_of_smallEtaleStalkPullbackRingMap_eq_zero (h : V ⟶ U)
    (hh : IsClosedImmersion B S hS h.hom) (y : GeometricPoint B S hS V.1)
    (z : geometricStalkRing B S hS (X := U) (geometricPointMap h.hom y))
    (hz : smallEtaleStalkPullbackRingMap B S hS h y z = 0) :
    ∃ (W : SmallEtale B S hS U.1)
      (w : (etaleSitePoint B S hS U.1 (geometricPointMap h.hom y) U.2).fiber.obj W)
      (s : (structurePresheaf B S hS U.1).obj (op W)),
      Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (hh.rep.snd W.1.hom))) s = 0 ∧
        (etaleSitePoint B S hS U.1 (geometricPointMap h.hom y) U.2).toPresheafFiber W w
          (smallEtaleRingedTopos B S hS U).O.obj s = z := by
  obtain ⟨W, w, s, rfl⟩ :=
    (etaleSitePoint B S hS U.1 (geometricPointMap h.hom y) U.2).toPresheafFiber_jointly_surjective
      (P := (smallEtaleRingedTopos B S hS U).O.obj) z
  let d : ChartDiagram B S hS V.1 U.1 h.hom :=
    ⟨(smallBaseChange B S hS h hh.rep).obj W, W, hh.rep.snd W.1.hom, hh.rep.w W.1.hom⟩
  let p := smallBaseChangeFiberInv B S hS h hh.rep y W w
  have hp : p.1 ≫ d.g = w.1 :=
    congrArg Subtype.val (smallBaseChangeFiberMap_smallBaseChangeFiberInv B S hS h hh.rep y W w)
  rw [smallEtaleStalkPullbackRingMap_toPresheafFiber B S hS h y d p w hp s,
    ← map_zero (ConcreteCategory.hom ((etaleSitePoint B S hS V.1 y V.2).toPresheafFiber d.U p
      (smallEtaleRingedTopos B S hS V).O.obj))] at hz
  obtain ⟨N, f, n, hn, hfz⟩ :=
    ((etaleSitePoint B S hS V.1 y V.2).toPresheafFiber_eq_iff' d.U p _ _).1 hz
  rw [map_zero] at hfz
  let Nn : SmallEtaleNeighborhood y := ⟨N, n.1, n.2⟩
  let Wn : SmallEtaleNeighborhood (geometricPointMap h.hom y) := ⟨W, w.1, w.2⟩
  let fn : Nn ⟶ (SmallEtaleNeighborhood.baseChange B S hS h hh.rep y).obj Wn :=
    ⟨f, congrArg Subtype.val hn⟩
  obtain ⟨V₀, ⟨k⟩⟩ := SmallEtaleNeighborhood.exists_baseChange_hom B S hS h hh y Nn
  obtain ⟨W₁, a, b, hab⟩ :=
    SmallEtaleNeighborhood.exists_baseChange_factorization B S hS h hh y V₀ Wn (k ≫ fn)
  have hab' : (smallBaseChange B S hS h hh.rep).map a.hom ≫ k.hom ≫ f =
      (smallBaseChange B S hS h hh.rep).map b.hom :=
    congrArg SmallEtaleNeighborhood.Hom.hom hab
  refine ⟨W₁.chart, ⟨W₁.point, W₁.point_comp⟩, (structurePresheaf B S hS U.1).map b.hom.op s,
    ?_, ?_⟩
  · have e1 := structurePresheaf_map_snd B S hS h hh.rep b.hom s
    have hfz' : (structurePresheaf B S hS V.1).map f.op
        (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s) = 0 := hfz
    rw [e1, ← hab']
    show (structurePresheaf B S hS V.1).map ((smallBaseChange B S hS h hh.rep).map a.hom).op
        ((structurePresheaf B S hS V.1).map k.hom.op ((structurePresheaf B S hS V.1).map f.op
          (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map d.g)) s))) = 0
    rw [hfz', map_zero]
    exact map_zero _
  · have hw : (etaleSitePoint B S hS U.1 (geometricPointMap h.hom y) U.2).fiber.map b.hom
        ⟨W₁.point, W₁.point_comp⟩ = w := Subtype.ext b.point_comp
    refine (ConcreteCategory.congr_hom
      ((etaleSitePoint B S hS U.1 (geometricPointMap h.hom y) U.2).toPresheafFiber_w b.hom
        ⟨W₁.point, W₁.point_comp⟩ (smallEtaleRingedTopos B S hS U).O.obj) s).trans ?_
    rw [hw]

/-- A morphism of presheaves whose base changes to schemes are `n`th-order thickenings is a
closed immersion. -/
theorem isClosedImmersion_of_presheaf_thickOrder {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {n : ℕ}
    (hf : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    IsClosedImmersion B S hS f :=
  MorphismProperty.relative_monotone
    (P := MorphismProperty.inverseImage (thickOrder.{u} n) (BigFppfOver.toScheme B S hS))
    (P' := MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))
    (fun _ _ _ hg => hg.1) _ hf

/-- A morphism of presheaves whose base changes to schemes are `n`th-order thickenings has
surjective base changes to schemes. -/
theorem presheaf_surjective_of_presheaf_thickOrder {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {n : ℕ}
    (hf : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
  MorphismProperty.relative_monotone
    (P := MorphismProperty.inverseImage (thickOrder.{u} n) (BigFppfOver.toScheme B S hS))
    (fun _ _ _ hg => ⟨(Stacks.Thickenings.IsNthOrderThickening.isThickening hg).2⟩) _ hf

/-- **The stalk maps of a finite-order thickening have nilpotent kernel.**  Let `h : V ⟶ U` be a
morphism of algebraic spaces every base change of which to a scheme is an `n`th-order thickening
of schemes, and let `ȳ` be a geometric point of `V`.  The kernel of the stalk map
`(𝒪_U)_{h(ȳ)} ⟶ (𝒪_V)_{ȳ}` has vanishing `(n + 1)`st power.

The kernel is the union, over the pointed étale charts `W` of `U`, of the germs of the kernels of
`Γ(W) ⟶ Γ(V ×_U W)`
(`AlgebraicGeometry.Space.exists_germ_eq_of_smallEtaleStalkPullbackRingMap_eq_zero`); this union is
directed, and each of those kernels has vanishing `(n + 1)`st power because `V ×_U W ⟶ W` is an
`n`th-order thickening of schemes
(`Stacks.Thickenings.ker_app_pow_eq_bot_of_isNthOrderThickening`). -/
theorem ker_smallEtaleStalkPullbackRingMap_pow_eq_bot (h : V ⟶ U) {n : ℕ}
    (hh : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf h.hom)
    (y : GeometricPoint B S hS V.1) :
    RingHom.ker (smallEtaleStalkPullbackRingMap B S hS h y) ^ (n + 1) = ⊥ := by
  classical
  have hci : IsClosedImmersion B S hS h.hom := isClosedImmersion_of_presheaf_thickOrder B S hS hh
  let Φ := etaleSitePoint B S hS U.1 (geometricPointMap h.hom y) U.2
  let O := (smallEtaleRingedTopos B S hS U).O.obj
  let J : ∀ W : SmallEtale B S hS U.1, Ideal ((structurePresheaf B S hS U.1).obj (op W)) :=
    fun W => RingHom.ker
      (Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (hci.rep.snd W.1.hom)))).hom
  let Q : ℕ → geometricStalkRing B S hS (X := U) (geometricPointMap h.hom y) → Prop := fun m x =>
    ∃ (W : SmallEtale B S hS U.1) (w : Φ.fiber.obj W)
      (s : (structurePresheaf B S hS U.1).obj (op W)),
      s ∈ J W ^ m ∧ Φ.toPresheafFiber W w O s = x
  -- restriction along a morphism of charts carries `J W ^ m` into `J W' ^ m`
  have hres : ∀ {W W' : SmallEtale B S hS U.1} (g : W' ⟶ W) (m : ℕ)
      (s : (structurePresheaf B S hS U.1).obj (op W)), s ∈ J W ^ m →
        (structurePresheaf B S hS U.1).map g.op s ∈ J W' ^ m := by
    intro W W' g m s hs
    have hle : Ideal.map ((structurePresheaf B S hS U.1).map g.op).hom (J W) ≤ J W' := by
      rw [Ideal.map_le_iff_le_comap]
      intro t ht
      show Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (hci.rep.snd W'.1.hom)))
        ((structurePresheaf B S hS U.1).map g.op t) = 0
      rw [structurePresheaf_map_snd B S hS h hci.rep g t]
      have ht' : Scheme.Γ.map (op ((BigFppfOver.toScheme B S hS).map (hci.rep.snd W.1.hom))) t
          = 0 := ht
      rw [ht']
      exact map_zero _
    have := Ideal.mem_map_of_mem ((structurePresheaf B S hS U.1).map g.op).hom hs
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hle m this
  -- two pointed charts have a common pointed refinement
  have := isCofiltered_smallEtaleNeighborhood B S hS U.1 U.2 (geometricPointMap h.hom y)
  have hgerm : ∀ {W W' : SmallEtale B S hS U.1} (g : W' ⟶ W) (w' : Φ.fiber.obj W')
      (w : Φ.fiber.obj W), Φ.fiber.map g w' = w → ∀ s : (structurePresheaf B S hS U.1).obj (op W),
        Φ.toPresheafFiber W' w' O ((structurePresheaf B S hS U.1).map g.op s) =
          Φ.toPresheafFiber W w O s := by
    intro W W' g w' w hw s
    rw [← hw]
    exact ConcreteCategory.congr_hom (Φ.toPresheafFiber_w g w' O) s
  -- two elements of `Q m` and `Q l` are germs of functions on one common pointed chart
  have hpair : ∀ {m l x x'}, Q m x → Q l x' → ∃ (W : SmallEtale B S hS U.1) (w : Φ.fiber.obj W)
      (s s' : (structurePresheaf B S hS U.1).obj (op W)),
      s ∈ J W ^ m ∧ s' ∈ J W ^ l ∧ Φ.toPresheafFiber W w O s = x ∧
        Φ.toPresheafFiber W w O s' = x' := by
    rintro m l x x' ⟨W₁, w₁, s₁, hs₁, rfl⟩ ⟨W₂, w₂, s₂, hs₂, rfl⟩
    let N₁ : SmallEtaleNeighborhood (geometricPointMap h.hom y) := ⟨W₁, w₁.1, w₁.2⟩
    let N₂ : SmallEtaleNeighborhood (geometricPointMap h.hom y) := ⟨W₂, w₂.1, w₂.2⟩
    let N := IsCofiltered.min N₁ N₂
    let w₃ : Φ.fiber.obj N.chart := ⟨N.point, N.point_comp⟩
    exact ⟨N.chart, w₃, _, _, hres (IsCofiltered.minToLeft N₁ N₂).hom m s₁ hs₁,
      hres (IsCofiltered.minToRight N₁ N₂).hom l s₂ hs₂,
      hgerm _ w₃ w₁ (Subtype.ext (IsCofiltered.minToLeft N₁ N₂).point_comp) s₁,
      hgerm _ w₃ w₂ (Subtype.ext (IsCofiltered.minToRight N₁ N₂).point_comp) s₂⟩
  have hadd : ∀ m x x', Q m x → Q m x' → Q m (x + x') := by
    intro m x x' hx hx'
    obtain ⟨W, w, s, s', hs, hs', rfl, rfl⟩ := hpair hx hx'
    exact ⟨W, w, s + s', Ideal.add_mem _ hs hs',
      map_add (ConcreteCategory.hom (Φ.toPresheafFiber W w O)) _ _⟩
  have hmul : ∀ m l x x', Q m x → Q l x' → Q (m + l) (x * x') := by
    intro m l x x' hx hx'
    obtain ⟨W, w, s, s', hs, hs', rfl, rfl⟩ := hpair hx hx'
    exact ⟨W, w, s * s', pow_add (J W) m l ▸ Ideal.mul_mem_mul hs hs',
      map_mul (ConcreteCategory.hom (Φ.toPresheafFiber W w O)) _ _⟩
  have hone : ∀ x ∈ RingHom.ker (smallEtaleStalkPullbackRingMap B S hS h y), Q 1 x := by
    intro x hx
    obtain ⟨W, w, s, hs, rfl⟩ :=
      exists_germ_eq_of_smallEtaleStalkPullbackRingMap_eq_zero B S hS h hci y x hx
    exact ⟨W, w, s, by rw [pow_one]; exact hs, rfl⟩
  have hpow : ∀ m, ∀ x ∈ RingHom.ker (smallEtaleStalkPullbackRingMap B S hS h y) ^ (m + 1),
      Q (m + 1) x := by
    intro m
    induction m with
    | zero => intro x hx; rw [zero_add, pow_one] at hx; exact hone x hx
    | succ m ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun a ha b hb => hmul _ 1 a b (ih a ha) (hone b hb))
        (fun a b => hadd _ a b)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨W, w, s, hs, rfl⟩ := hpow n x hx
  have hW : J W ^ (n + 1) = ⊥ :=
    Stacks.Thickenings.ker_app_pow_eq_bot_of_isNthOrderThickening (hh.property_snd W.1.hom) ⊤
  rw [hW, Ideal.mem_bot] at hs
  rw [hs, Ideal.mem_bot]
  exact map_zero _

/-- **The stalk maps of a finite-order thickening are surjective with nilpotent kernel.**  For a
morphism `h : V ⟶ U` of algebraic spaces every base change of which to a scheme is an `n`th-order
thickening of schemes, and a geometric point `ȳ` of `V`, the fibre `𝒪_{U, h(ȳ)} ⟶ 𝒪_{V, ȳ}` of
the structure map is surjective with nilpotent kernel. -/
theorem surjective_and_isNilpotent_ker_stalkStructureMap (h : V ⟶ U) {n : ℕ}
    (hh : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf h.hom)
    (y : GeometricPoint B S hS V.1) :
    Function.Surjective (stalkStructureMap B S hS h y).hom ∧
      IsNilpotent (RingHom.ker (stalkStructureMap B S hS h y).hom) := by
  rw [stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap]
  exact ⟨surjective_smallEtaleStalkPullbackRingMap_of_isClosedImmersion B S hS h y
      (isClosedImmersion_of_presheaf_thickOrder B S hS hh),
    ⟨n + 1, by
      rw [Ideal.zero_eq_bot]; exact ker_smallEtaleStalkPullbackRingMap_pow_eq_bot B S hS h hh y⟩⟩

end Nilpotent

end AlgebraicGeometry.Space

end
