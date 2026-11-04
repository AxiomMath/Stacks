module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.ModuleFacts
public import StacksFrontier.AlgebraicGeometry.Chow.SecondAdamsSymmetricFiltration
public import StacksFrontier.AlgebraicGeometry.Chow.VectorBundleKZeroPullbackComp
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.AlgebraicGeometry.Perfect.GenericFreeCohomology
public import StacksFrontier.AlgebraicGeometry.Thickenings.ImmersionConormalIdentification
public import StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairSplitConormalSequence

/-!
# The class of a conormal sheaf in `K₀(Vect(-))` along smooth morphisms

Two facts about conormal sheaves of immersions between smooth schemes, read in the Grothendieck
ring `K₀(Vect(Z))` of finite locally free modules.

First, if `i : Z ⟶ X` is an immersion of schemes over `S` with `X` and `Z` smooth over `S`, the
conormal sheaf `𝒞_{Z/X}` is finite locally free: by [Stacks, Tag 06AA] it is the kernel of the
surjection `i^*Ω_{X/S} ⟶ Ω_{Z/S}` of finite locally free modules.

Second, let `i : Z ⟶ X` and `j : Z ⟶ Y` be immersions with `i ≫ p = j` for a smooth morphism
`p : X ⟶ Y`. By [Stacks, Tag 067W] the conormal sequence
`0 ⟶ 𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0` is short exact, so, when `𝒞_{Z/Y}` is finite locally
free, `[𝒞_{Z/X}] = [𝒞_{Z/Y}] + i^*[Ω_{X/Y}]` in `K₀(Vect(Z))`. In particular, if the class of
`𝒞_{Z/Y}` is the pullback along `i` of a class of `K₀(Vect(X))`, so is the class of `𝒞_{Z/X}`.
This is the step of the proof of [Stacks, Tag 0FIR] that passes from `Z ⟶ X` to
`Z ⟶ X × 𝐆(n - r, n)`.

## Main results

* `Stacks.Conormal.sheafOfModules_isFiniteLocallyFree_conormalSheaf_of_smooth` and
  `Stacks.Conormal.isFiniteLocallyFree_conormalSheaf_of_smooth`: the conormal sheaf of an
  immersion of smooth `S`-schemes is finite locally free, at the two spellings of finite local
  freeness of the library.
* `Stacks.Conormal.classOf_conormalSheaf_of_smooth`: `[𝒞_{Z/X}] = [𝒞_{Z/Y}] + i^*[Ω_{X/Y}]`.
* `Stacks.Conormal.exists_pullbackRingHom_eq_classOf_conormalSheaf_of_smooth`: a class of
  `𝒞_{Z/Y}` pulled back along `i` makes one of `𝒞_{Z/X}`.

## Implementation notes

The conormal sheaf is `Stacks.Conormal.conormalSheaf`, the conormal sheaf of [Stacks, Tag 01R2].
The short exact sequence of [Stacks, Tag 06AA] in the library starts at the sectionwise
presentation `Stacks.AlgebraicGeometry.RegularIdealSheaf.conormalSheaf`, and the one of
[Stacks, Tag 067W] at the conormal sheaf of a formally unramified morphism
`Stacks.Thickenings.universalConormalSheaf`; both are identified with
`Stacks.Conormal.conormalSheaf` by the canonical isomorphisms
`Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso` and
`Stacks.Thickenings.immersionConormalSheafIsoUniversalConormalSheaf`, and isomorphic modules
have the same finite local freeness and the same class.

## References

* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA)
* [Stacks Project, Tag 067W](https://stacks.math.columbia.edu/tag/067W)
* [Stacks Project, Tag 0FIR](https://stacks.math.columbia.edu/tag/0FIR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Conormal

/-- **The conormal sheaf of an immersion of smooth schemes is finite locally free.** For an
immersion `i : Z ⟶ X` over `p : X ⟶ S` with `p` and `i ≫ p` smooth, `𝒞_{Z/X}` is the kernel
of the surjection `i^*Ω_{X/S} ⟶ Ω_{Z/S}` of [Stacks, Tag 06AA], whose source and target are
finite locally free. -/
theorem sheafOfModules_isFiniteLocallyFree_conormalSheaf_of_smooth {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (p : X ⟶ S) [Smooth p] [Smooth (i ≫ p)] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Z.ringCatSheaf)
      (conormalSheaf i : Z.Modules) := by
  have hS := Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i p inferInstance
  have := hS.epi_g
  have h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := Z.ringCatSheaf) (Stacks.ConormalSequenceRight.conormalShortComplex i p).X₂ :=
    VectorBundleKZero.isFiniteLocallyFree_toSheaf
      (VectorBundleKZero.isFiniteLocallyFree_pullback i _
        (have := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials p
         Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _))
  have h₃ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := Z.ringCatSheaf) (Stacks.ConormalSequenceRight.conormalShortComplex i p).X₃ :=
    Scheme.Hom.isFiniteLocallyFree_relativeDifferentials (i ≫ p)
  have hker := isFiniteLocallyFree_kernel_of_epi_of_isFiniteLocallyFree
    (Stacks.ConormalSequenceRight.conormalShortComplex i p).g h₂ h₃
  have e := IsLimit.conePointUniqueUpToIso hS.fIsKernel (limit.isLimit _)
  have h₁ := @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso _ _ _ e.symm hker
  exact @AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso _ _ _
    (Stacks.ConormalSequenceUnramifiedPair.conormalSheafComparisonIso i) h₁

/-- **The conormal sheaf of an immersion of smooth schemes is finite locally free**, at the
spelling of finite local freeness `K₀(Vect(Z))` is built over. -/
theorem isFiniteLocallyFree_conormalSheaf_of_smooth {Z X S : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (p : X ⟶ S) [Smooth p] [Smooth (i ≫ p)] :
    Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Z.ringCatSheaf)
      (conormalSheaf i : Z.Modules) :=
  have := sheafOfModules_isFiniteLocallyFree_conormalSheaf_of_smooth i p
  Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y)
  [IsImmersion i] [IsImmersion j] [Smooth p]

/-- **The conormal sequence of `Z ⟶ X ⟶ Y` in `K₀(Vect(Z))`.** For immersions `i : Z ⟶ X` and
`j : Z ⟶ Y` with `i ≫ p = j` and `p` smooth, the short exact sequence
`0 ⟶ 𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0` of [Stacks, Tag 067W] gives
`[𝒞_{Z/X}] = [𝒞_{Z/Y}] + i^*[Ω_{X/Y}]`, as soon as `𝒞_{Z/Y}` is finite locally free. -/
theorem classOf_conormalSheaf_of_smooth (h : i ≫ p = j)
    (hj : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Z.ringCatSheaf)
      (conormalSheaf j : Z.Modules)) :
    VectorBundleKZero.classOf Z (conormalSheaf i) =
      VectorBundleKZero.classOf Z (conormalSheaf j) +
        VectorBundleKZero.pullbackRingHom i
          (VectorBundleKZero.classOf X (Scheme.Hom.relativeDifferentials p)) := by
  have hp : FormallySmooth p :=
    ((Stacks.Smooth.smooth_iff_locallyOfFinitePresentation_and_formallySmooth p).mp
      inferInstance).2
  have hS := Stacks.ConormalSequenceUnramifiedPair.shortExact_of_comp_eq_zero_of_exact i j p h hp
  set S := ShortComplex.mk _ _
    (Stacks.ConormalSequenceUnramifiedPair.conormalSequenceComp_eq_zero i j p h) with hSdef
  have := hS.mono_f
  have := hS.epi_g
  have eY : (conormalSheaf j : Z.Modules) ≅ S.X₁ :=
    Stacks.Thickenings.immersionConormalSheafIsoUniversalConormalSheaf j
  have eX : (conormalSheaf i : Z.Modules) ≅ S.X₂ :=
    Stacks.Thickenings.immersionConormalSheafIsoUniversalConormalSheaf i
  have hΩ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Hom.relativeDifferentials p) :=
    have := Scheme.Hom.isFiniteLocallyFree_relativeDifferentials p
    Stacks.StalkFreeBridge.finiteLocallyFree_isFiniteLocallyFree _
  have h₃ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Z.ringCatSheaf) S.X₃ :=
    VectorBundleKZero.isFiniteLocallyFree_pullback i _ hΩ
  have h₁ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Z.ringCatSheaf) S.X₁ :=
    @Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ _ _ eY hj
  have h₂ : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Z.ringCatSheaf) S.X₂ :=
    VectorBundleKZero.isFiniteLocallyFree_ofSheaf
      (Stacks.Chow.GenuineChern.isFiniteLocallyFree_of_shortExact S hS
        (VectorBundleKZero.isFiniteLocallyFree_toSheaf h₁)
        (VectorBundleKZero.isFiniteLocallyFree_toSheaf h₃))
  have hrel := VectorBundleKZero.classOf_shortExact S.f S.g S.zero h₁ h₂ h₃ hS.exact
  rw [VectorBundleKZero.classOf_eq_of_iso eX
      (@Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ _ _ eX.symm h₂),
    VectorBundleKZero.classOf_eq_of_iso eY hj, hrel,
    VectorBundleKZero.pullbackRingHom_classOf i _ hΩ]

/-- **A class of `𝒞_{Z/Y}` pulled back along `i` gives one of `𝒞_{Z/X}`.** For immersions
`i : Z ⟶ X` and `j : Z ⟶ Y` with `i ≫ p = j` and `p` smooth, if `𝒞_{Z/Y}` is finite locally free
and its class in `K₀(Vect(Z))` is `i^*β` for some `β ∈ K₀(Vect(X))`, then the class of `𝒞_{Z/X}`
is `i^*(β + [Ω_{X/Y}])`. -/
theorem exists_pullbackRingHom_eq_classOf_conormalSheaf_of_smooth (h : i ≫ p = j)
    (hj : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Z.ringCatSheaf)
      (conormalSheaf j : Z.Modules))
    (hβ : ∃ β : VectorBundleKZero X,
      VectorBundleKZero.pullbackRingHom i β = VectorBundleKZero.classOf Z (conormalSheaf j)) :
    ∃ β : VectorBundleKZero X,
      VectorBundleKZero.pullbackRingHom i β = VectorBundleKZero.classOf Z (conormalSheaf i) := by
  obtain ⟨β, hβ⟩ := hβ
  refine ⟨β + VectorBundleKZero.classOf X (Scheme.Hom.relativeDifferentials p), ?_⟩
  rw [map_add, hβ, classOf_conormalSheaf_of_smooth i j p h hj]

end Stacks.Conormal

end
