module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherent
public import StacksFrontier.AlgebraicGeometry.Pullback.AffineOpens
public import StacksFrontier.Homology.PseudoCoherent.Relative.TorIndependentBaseChange
public import StacksFrontier.Homology.Tor.Presentation
public import StacksFrontier.RingTheory.Tor.Balancing
import StacksFrontier.Homology.PseudoCoherent.Relative.TowerModule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat base change of a pseudo-coherent morphism

A flat base change of a pseudo-coherent morphism of schemes is pseudo-coherent (Stacks 0680).

## Main results

* `Algebra.PseudoCoherent.of_isPushout_of_flat`: the algebra content, that a pseudo-coherent
  ring map `A → B` stays pseudo-coherent after a flat base change `A → A'`, the base-changed
  algebra being presented as a pushout `B' = A' ⊗_A B`.
* `AlgebraicGeometry.pseudoCoherent_of_isPullback_of_flat`: **Stacks 0680**, in a cartesian
  square of schemes whose base map is flat, the base change of a pseudo-coherent morphism is
  pseudo-coherent.
* `AlgebraicGeometry.pseudoCoherent_pullback_snd`: the same in the `pullback` spelling.

## Implementation notes

The algebra statement is Stacks 067A, which carries relative pseudo-coherence over `A` of an
object of `D(B)` to relative pseudo-coherence over `A'` of its derived base change, for a base
change that is merely Tor independent from `B`. A flat `A`-algebra `A'` is Tor independent from
every `A`-algebra: `Torᵢ^A(B, A')` is `Torᵢ^A(A', B)` by the symmetry of Tor (Stacks 00M3), and
the latter vanishes in positive degrees because tensoring with a flat module preserves the
exactness of a projective resolution. Applied to `B` as a module over itself, Stacks 067A then
gives relative pseudo-coherence of the derived base change of `B`, which is `A' ⊗_A B` in degree
zero because `B → A' ⊗_A B` is again flat; and relative pseudo-coherence of `A' ⊗_A B` over
itself together with finite type is pseudo-coherence of `A' → A' ⊗_A B`.

The reduction of the geometric statement to the algebra one is affine-local around points of the
source: pseudo-coherence of a morphism of schemes may be checked on one compatible pair of
affine opens around each point of the source
(`AlgebraicGeometry.HasRingHomProperty.iff_exists_appLE`, available because pseudo-coherence of
ring maps is stable under composition with a localization away from an element), and over an
affine open `V` of the base, an affine open `U` of `X` over `V` and an affine open `V'` of `S'`
over `V`, the sections over `g'⁻¹U ∩ f'⁻¹V'` are the tensor product
`Γ(X, U) ⊗_{Γ(S, V)} Γ(S', V')`.

## References

* [The Stacks Project, Lemma 37.60.3 (0680)](https://stacks.math.columbia.edu/tag/0680)
* [The Stacks Project, Lemma 15.83.12 (067A)](https://stacks.math.columbia.edu/tag/067A)
* [The Stacks Project, Lemma 10.75.5 (00M3)](https://stacks.math.columbia.edu/tag/00M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry TensorProduct
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence

universe u v

namespace RingHom

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- A flat `R`-algebra `B` is Tor independent from every `R`-algebra `A`: the vanishing of
`Torᵢ^R(A, B)` for `i > 0` is the vanishing of `Torᵢ^R(B, A)` by the symmetry of Tor, and that
holds because tensoring with a flat module preserves the exactness of a projective
resolution. -/
@[sga "7 VIII 1.2" "special case"]
private lemma torIndependent_of_flat_right {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] [Module.Flat R B] :
    TorIndependent R A B := by
  rw [torIndependent_iff_isZero_tor]
  intro i hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  obtain ⟨e⟩ := tor_symm_canonically_iso R (k + 1)
  refine IsZero.of_iso (isZero_Tor_succ_of_flat (ModuleCat.of R B) (ModuleCat.of R A) k) ?_
  simpa [Functor.flip] using (e.app (ModuleCat.of R A)).app (ModuleCat.of R B)

/-- Along a flat ring map, derived extension of scalars takes the source, as a module over
itself in degree zero, to the target, as a module over itself in degree zero: flatness makes
extension of scalars exact, so it commutes with the degree-zero single-object functor. -/
private def derivedExtensionScalarsRingSingleIsoOfFlat {S B : Type u} [CommRing S] [CommRing B]
    (f : S →+* B) (hf : f.Flat) :
    (derivedExtensionScalarsGeneral.{u, u, u} f).functor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} S) 0).obj (ModuleCat.of S S)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B) := by
  let F := ModuleCat.extendScalars.{u, u, u} f
  letI : Algebra S B := f.toAlgebra
  have : Module.Flat S B := hf
  have : F.Additive :=
    ⟨fun {_ _ g h} ↦ ModuleCat.hom_ext <|
      LinearMap.baseChange_add (A := B) (f := g.hom) (g := h.hom)⟩
  have hexact : ∀ T : ShortComplex (ModuleCat.{u} S), T.Exact → (T.map F).Exact := by
    intro T hT
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
    exact Module.Flat.lTensor_exact B hT
  have hlimits := ((Functor.exact_tfae F).out 2 4).mp hexact
  have : PreservesFiniteLimits F := hlimits.1
  have : PreservesFiniteColimits F := hlimits.2
  exact (PseudoCoherence.derivedExtensionIsoOfExact f).app _ ≪≫
    (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).mapIso (RingHom.extendScalarsRingIso f)

/-- A flat base change of a pseudo-coherent ring map is pseudo-coherent, in the concrete model
`A' ⊗[A] B` of the base-changed algebra.

A flat `A`-algebra is Tor independent from `B`, so Stacks 067A carries relative pseudo-coherence
of `B` over `A` to relative pseudo-coherence of `A' ⊗[A] B` over `A'`; the derived base change of
`B` in degree zero is `A' ⊗[A] B` in degree zero because `B → A' ⊗[A] B` is again flat. -/
@[sga "6 III 1.1.3" "Clause (ii)",
  sga "6 III 1.10" "special case",
  sga "6 III 4.7" "(a), special case"]
private theorem _root_.Algebra.PseudoCoherent.baseChange_of_flat
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] [Module.Flat A A']
    [h : Algebra.PseudoCoherent A B] :
    letI : Algebra A' (A' ⊗[A] B) := Algebra.TensorProduct.leftAlgebra
    Algebra.PseudoCoherent A' (A' ⊗[A] B) := by
  let : Algebra A' (A' ⊗[A] B) := Algebra.TensorProduct.leftAlgebra
  obtain ⟨_, hrel⟩ := Algebra.pseudoCoherent_iff_exists_isModuleRelativelyPseudoCoherent.mp h
  have hfFlat : (Algebra.TensorProduct.includeRight.toRingHom : B →+* A' ⊗[A] B).Flat :=
    flat_algebraMap_iff.mpr <| Module.Flat.isBaseChange A B A' (A' ⊗[A] B)
      (Algebra.IsPushout.out (R := A) (S := B) (R' := A') (S' := A' ⊗[A] B))
  have hmain :=
    PseudoCoherence.derivedExtensionScalars_preserves_relativelyPseudoCoherent_of_torIndependent
      (R := A) (A := B) (R' := A')
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B))
      (torIndependent_of_flat_right (R := A) (A := B) (B := A'))
  dsimp only at hmain
  exact Algebra.pseudoCoherent_iff_isModuleRelativelyPseudoCoherent.mpr fun m ↦
    isRelativelyPseudoCoherentFrom_of_iso (derivedExtensionScalarsRingSingleIsoOfFlat _ hfFlat) m
      (hmain.2 hrel m)

/-- **The algebra content of Stacks 0680.** Let `A → B` be a pseudo-coherent ring map and let
`A → A'` be flat. Then the base change `A' → B'` is pseudo-coherent, for any presentation of
`B'` as the pushout `A' ⊗_A B`. -/
theorem _root_.Algebra.PseudoCoherent.of_isPushout_of_flat
    (A B : Type u) {A' : Type u} {B' : Type v} [CommRing A] [CommRing B] [CommRing A']
    [CommRing B'] [Algebra A B] [Algebra A A'] [Algebra A B'] [Algebra B B'] [Algebra A' B']
    [IsScalarTower A B B'] [IsScalarTower A A' B']
    [Algebra.IsPushout A A' B B'] [Module.Flat A A']
    [Algebra.PseudoCoherent A B] :
    Algebra.PseudoCoherent A' B' :=
  (Algebra.PseudoCoherent.baseChange_of_flat (A := A) (B := B) (A' := A')).equiv
    (Algebra.IsPushout.equiv A A' B B')

end RingHom

namespace AlgebraicGeometry

/-- **Stacks 0680.** A flat base change of a pseudo-coherent morphism of schemes is
pseudo-coherent: if `f : X ⟶ S` is pseudo-coherent, `g : S' ⟶ S` is flat and the square with
sides `g' : X' ⟶ X` and `f' : X' ⟶ S'` is cartesian, then `f'` is pseudo-coherent. -/
@[stacks 0680]
theorem pseudoCoherent_of_isPullback_of_flat {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (sq : IsPullback g' f' f g) [Flat g] [PseudoCoherent f] :
    PseudoCoherent f' := by
  refine (HasRingHomProperty.iff_exists_appLE (P := @PseudoCoherent)
    RingHom.pseudoCoherent_stableUnderCompositionWithLocalizationAway.left).mpr fun x ↦ ?_
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show f.base (g'.base x) ∈ (⊤ : S.Opens) from trivial)
  have hbase : g.base (f'.base x) = f.base (g'.base x) :=
    (congrArg (fun q : X' ⟶ S => q.base x) sq.w).symm
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show g'.base x ∈ f ⁻¹ᵁ V from hxV)
  obtain ⟨V', hV', hxV', hV'V⟩ := exists_isAffineOpen_mem_and_subset
    (show f'.base x ∈ g ⁻¹ᵁ V by simpa [hbase] using hxV)
  have hsq := isPushout_appLE_of_isPullback sq hV hU hUV hV' hV'V rfl
  have hcomp : (g'.appLE U (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') inf_le_left).hom.comp
        (f.appLE V U hUV).hom =
      (f'.appLE V' (g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') inf_le_right).hom.comp
        (g.appLE V V' hV'V).hom := by
    simpa using congrArg CommRingCat.Hom.hom hsq.w
  refine ⟨⟨V', hV'⟩, ⟨g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V',
      IsAffineOpen.inf_preimage_of_isPullback sq hV hU hUV hV' hV'V rfl⟩,
    ⟨hxU, hxV'⟩, inf_le_right, ?_⟩
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(S', V') := (g.appLE V V' hV'V).hom.toAlgebra
  let : Algebra Γ(X, U) Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') :=
    (g'.appLE U _ inf_le_left).hom.toAlgebra
  let : Algebra Γ(S', V') Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') :=
    (f'.appLE V' _ inf_le_right).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') :=
    ((g'.appLE U _ inf_le_left).hom.comp (f.appLE V U hUV).hom).toAlgebra
  have : IsScalarTower Γ(S, V) Γ(X, U) Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, V) Γ(S', V') Γ(X', g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ V') :=
    IsScalarTower.of_algebraMap_eq' hcomp
  have := algebra_isPushout_appLE_of_isPullback sq hV hU hUV hV' hV'V rfl
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  have : Module.Flat Γ(S, V) Γ(S', V') :=
    HasRingHomProperty.appLE @Flat g ‹Flat g› ⟨V, hV⟩ ⟨V', hV'⟩ hV'V
  exact (HasRingHomProperty.appLE @PseudoCoherent f ‹PseudoCoherent f› ⟨V, hV⟩ ⟨U, hU⟩
    hUV).of_isPushout_of_flat

/-- The `pullback` spelling of `AlgebraicGeometry.pseudoCoherent_of_isPullback_of_flat`: the
projection to a flat base from the fibre product of a pseudo-coherent morphism with it is
pseudo-coherent. -/
theorem pseudoCoherent_pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [Flat g]
    [PseudoCoherent f] : PseudoCoherent (Limits.pullback.snd f g) :=
  pseudoCoherent_of_isPullback_of_flat (IsPullback.of_hasPullback f g)

end AlgebraicGeometry

end
