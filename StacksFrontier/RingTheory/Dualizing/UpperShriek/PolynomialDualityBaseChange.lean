module

public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.RingTheory.Dualizing.Complexes.Uniqueness
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Homothety
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.MvPolynomialBaseChange
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
import all StacksFrontier.Homology.Perfect.SystemDuality

/-!
# Flat base change of derived Hom into a dualizing complex, on all of `D_Coh`

Let `A` be a Noetherian ring, let `ω` be a dualizing complex for `A`, let `P = A[x_1, …, x_n]`
and write `E` for derived extension of scalars `- ⊗_A^L P`, computed degreewise because `P` is
free over `A`.  The base-change morphism of [stacks 0E1X]

`RHom_A(K, ω) ⊗_A^L P ⟶ RHom_P(K ⊗_A^L P, ω ⊗_A^L P)`

is invertible for **every** `K` with finite cohomology in every degree, that is, for every object
of `D_Coh(A)` — with no boundedness hypothesis.

## Main results

* `Dualizing.isIso_mvPolynomialDerivedHomBaseChange_of_finiteCohomology` — the displayed
  morphism is invertible at every object of `D_Coh(A)`.
* `Dualizing.mvPolynomialDualityBaseChangeNatIso` — the same, as an isomorphism of functors
  `D_Coh(A)ᵒᵖ ⥤ D(P)`: `RHom_A(-, ω) ⊗_A^L P ≅ RHom_P(- ⊗_A^L P, ω ⊗_A^L P)`.

## Implementation notes

[stacks 0A6A], `Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange`, is unconditional in
this library, but its flat case asks for `K` to be *pseudo-coherent*, which over a Noetherian
ring means bounded above with finite cohomology.  Objects of `D_Coh(A)` need not be bounded
above, and the boundedness is removed here exactly as the source removes it: the cohomology of
either side in a fixed degree depends only on a truncation of `K`, so it suffices to know the
comparison on every `τ^{≤ m}K` — each of which *is* pseudo-coherent,
`Dualizing.isPseudoCoherent_truncLEObj` — together with a uniform cohomological bound on the
complementary tails `τ^{≥ m+1}K`.  That bookkeeping is `Dualizing.isIso_app_of_isLE_tail`.

The two bounds on the tails come from the finite injective dimension of a dualizing complex:
`RHom_A(-, ω)` carries `IsGE (m+1)` to `IsLE (b - m - 1)` by
`Dualizing.dualizingDerivedHom_isLE_of_isGE`, and the same bound exchange over `P` applies to
`ω ⊗_A^L P`, which is a dualizing complex for `P` by
`Dualizing.mvPolynomialBaseChange_isDualizingComplex`.  Derived extension of scalars along the
flat map `A → P` moves both bounds, by `Dualizing.mapDerivedCategory_isLE` and
`Dualizing.mapDerivedCategory_isGE`.

Both functors being compared are contravariant and carry distinguished triangles to
distinguished triangles: for derived Hom this is
`StacksDraft.DerivedHom.exists_distinguished_derivedHom_overRing`, reached by `import all`
because no `CategoryTheory.Functor.CommShift` is available for derived internal Hom in either
variable, so the statement cannot be packaged as a `CategoryTheory.Functor.IsTriangulated`
instance; derived extension of scalars along a flat map is triangulated outright.

## References

* [Stacks Project, Tag 0A6A](https://stacks.math.columbia.edu/tag/0A6A)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
* [Stacks Project, Tag 0A7J](https://stacks.math.columbia.edu/tag/0A7J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

open StacksDraft.DerivedHom

/-! ### Invertibility of a contravariant transformation from its truncations -/

/-- **A transformation of contravariant functors invertible on every upper truncation of `K`, and
whose values on the complementary tails are uniformly bounded above, is invertible at `K`.**  This
is the bookkeeping that removes a boundedness hypothesis from a comparison of two contravariant
functors out of a derived category: in each cohomological degree `i`, choosing `m` large enough
that both tails `τ^{≥ m+1}K` contribute nothing in degrees `i` and `i+1` identifies the degree-`i`
cohomology of both functors at `K` with their cohomology at `τ^{≤ m}K`.

This is the contravariant, bounded-above counterpart of
`StacksDraft.DerivedHom.isIso_app_of_isGE_truncGE`, which handles covariant functors with
bounded-below tails. -/
theorem isIso_app_of_isLE_tail
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : (DerivedCategory C)ᵒᵖ ⥤ DerivedCategory D)
    (hFtri : ∀ (T : Triangle (DerivedCategory C)),
      T ∈ distTriang _ → ∃ δ, Triangle.mk (F.map T.mor₂.op) (F.map T.mor₁.op) δ ∈
        distTriang (DerivedCategory D))
    (hGtri : ∀ (T : Triangle (DerivedCategory C)),
      T ∈ distTriang _ → ∃ δ, Triangle.mk (G.map T.mor₂.op) (G.map T.mor₁.op) δ ∈
        distTriang (DerivedCategory D))
    (α : F ⟶ G) (K : DerivedCategory C)
    (hα : ∀ m : ℤ, IsIso (α.app (Opposite.op
      ((DerivedCategory.TStructure.t.truncLE m).obj K))))
    (hF : ∃ c : ℤ, ∀ m : ℤ, (F.obj (Opposite.op
      ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K))).IsLE (c - m - 1))
    (hG : ∃ c : ℤ, ∀ m : ℤ, (G.obj (Opposite.op
      ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K))).IsLE (c - m - 1)) :
    IsIso (α.app (Opposite.op K)) := by
  obtain ⟨cF, hcF⟩ := hF
  obtain ⟨cG, hcG⟩ := hG
  apply (DerivedCategory.isIso_iff _ _).mpr
  intro i
  let m : ℤ := max cF cG - i + 1
  let t := DerivedCategory.TStructure.t (C := C)
  let T : Triangle (DerivedCategory C) := Triangle.mk
    ((t.truncLEι m).app K) ((t.truncGEπ (m + 1)).app K)
    ((t.truncGEδLE m (m + 1) rfl).app K)
  have hT : T ∈ distTriang (DerivedCategory C) :=
    t.triangleLEGE_distinguished m (m + 1) rfl K
  have hmap (H : (DerivedCategory C)ᵒᵖ ⥤ DerivedCategory D)
      (hHtri : ∀ (T : Triangle (DerivedCategory C)), T ∈ distTriang _ →
        ∃ δ, Triangle.mk (H.map T.mor₂.op) (H.map T.mor₁.op) δ ∈
          distTriang (DerivedCategory D))
      (c : ℤ)
      (hcut : (H.obj (Opposite.op ((t.truncGE (m + 1)).obj K))).IsLE (c - m - 1))
      (hcuti : i > c - m - 1) :
      IsIso ((DerivedCategory.homologyFunctor D i).map
        (H.map ((t.truncLEι m).app K).op)) := by
    obtain ⟨δ, hδ⟩ := hHtri T hT
    have hz : IsZero ((DerivedCategory.homologyFunctor D i).obj
        (H.obj (Opposite.op ((t.truncGE (m + 1)).obj K)))) :=
      (DerivedCategory.isLE_iff _ _).mp hcut i hcuti
    have hz' : IsZero ((DerivedCategory.homologyFunctor D (i + 1)).obj
        (H.obj (Opposite.op ((t.truncGE (m + 1)).obj K)))) :=
      (DerivedCategory.isLE_iff _ _).mp hcut (i + 1) (by omega)
    have hmono : Mono ((DerivedCategory.homologyFunctor D i).map (H.map T.mor₁.op)) :=
      (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff
        (Triangle.mk (H.map T.mor₂.op) (H.map T.mor₁.op) δ) hδ i).mpr
        (hz.eq_of_src _ _)
    have hepi : Epi ((DerivedCategory.homologyFunctor D i).map (H.map T.mor₁.op)) :=
      (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff
        (Triangle.mk (H.map T.mor₂.op) (H.map T.mor₁.op) δ) hδ i (i + 1) rfl).mpr
        (hz'.eq_of_tgt _ _)
    have hiso : IsIso ((DerivedCategory.homologyFunctor D i).map (H.map T.mor₁.op)) :=
      isIso_of_mono_of_epi _
    change IsIso ((DerivedCategory.homologyFunctor D i).map
      (H.map ((t.truncLEι m).app K).op)) at hiso
    exact hiso
  have hFmap := hmap F hFtri cF (hcF m) (by dsimp [m]; omega)
  have hGmap := hmap G hGtri cG (hcG m) (by dsimp [m]; omega)
  have hw : (DerivedCategory.homologyFunctor D i).map (α.app (Opposite.op K)) ≫
      (DerivedCategory.homologyFunctor D i).map (G.map ((t.truncLEι m).app K).op) =
    (DerivedCategory.homologyFunctor D i).map (F.map ((t.truncLEι m).app K).op) ≫
      (DerivedCategory.homologyFunctor D i).map
        (α.app (Opposite.op ((t.truncLE m).obj K))) := by
    simpa only [Functor.id_obj, Functor.map_comp] using (congrArg
      ((DerivedCategory.homologyFunctor D i).map)
        (α.naturality ((t.truncLEι m).app K).op)).symm
  have hαm : IsIso ((DerivedCategory.homologyFunctor D i).map
      (α.app (Opposite.op ((t.truncLE m).obj K)))) := by
    have := hα m
    infer_instance
  exact IsIso.of_isIso_fac_right hw

/-! ### The degreewise model of extension of scalars to a polynomial algebra -/

variable (A : Type u) [CommRing A]

/-- Extension of scalars along `A → A[x_1, …, x_n]` is flat, the polynomial algebra being free
over its coefficient ring, so it preserves finite limits. -/
theorem preservesFiniteLimits_extendScalars_mvPolynomialC (n : ℕ) :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u}
      (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)) :=
  extendScalars_preservesFiniteLimits_of_flat' _ (RingHom.flat_algebraMap_iff.mpr inferInstance)

attribute [local instance] preservesFiniteLimits_extendScalars_mvPolynomialC

/-- The comparison exhibiting `Dualizing.mvPolynomialExtension` as the total left derived functor
of termwise extension of scalars.  It is invertible, extension of scalars along a flat map being
exact. -/
def mvPolynomialExtensionFactors (n : ℕ) :
    DerivedCategory.Q ⋙ mvPolynomialExtension A n ≅
      (ModuleCat.extendScalars.{u, u, u}
          (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (ModuleCat.extendScalars.{u, u, u}
    (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).mapDerivedCategoryFactors

/-- `Dualizing.mvPolynomialExtension` is the total left derived functor of termwise extension of
scalars, the comparison being the isomorphism `Dualizing.mvPolynomialExtensionFactors`. -/
theorem mvPolynomialExtension_isLeftDerivedFunctor (n : ℕ) :
    (mvPolynomialExtension A n).IsLeftDerivedFunctor (mvPolynomialExtensionFactors A n).hom
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _
    (ModuleCat.extendScalars.{u, u, u}
      (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).mapDerivedCategoryFactors

/-- Extension of scalars to a polynomial algebra commutes with the shift on derived
categories. -/
@[instance_reducible]
def mvPolynomialExtensionCommShift (n : ℕ) : (mvPolynomialExtension A n).CommShift ℤ :=
  inferInstanceAs (((ModuleCat.extendScalars.{u, u, u}
    (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).mapDerivedCategory).CommShift ℤ)

attribute [local instance] mvPolynomialExtensionCommShift

/-- Extension of scalars to a polynomial algebra is exact, hence triangulated on derived
categories. -/
theorem mvPolynomialExtension_isTriangulated (n : ℕ) :
    (mvPolynomialExtension A n).IsTriangulated :=
  inferInstanceAs (((ModuleCat.extendScalars.{u, u, u}
    (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)).mapDerivedCategory).IsTriangulated)

attribute [local instance] mvPolynomialExtension_isTriangulated

/-- The tail bound for derived Hom into an object of injective amplitude `[a, b]`. -/
private theorem dualizingDerivedHom_isLE_sub_sub (R : Type u) [CommRing R]
    (ω X : DerivedCategory (ModuleCat.{u} R)) (m a b : ℤ) (hX : X.IsGE (m + 1))
    (hω : StacksDraft.InjectiveDimension.HasInjectiveAmplitude ω a b) :
    ((dualizingDerivedHomFunctor.{u, u} R ω).obj (Opposite.op X)).IsLE (b - m - 1) := by
  simpa only [sub_add_eq_sub_sub] using
    dualizingDerivedHom_isLE_of_isGE.{u, u} R ω X (m + 1) a b hX hω

/-! ### Flat base change of derived Hom on `D_Coh` -/

/-- **Flat base change of derived Hom into a dualizing complex, on all of `D_Coh(A)`.**  Let `A`
be Noetherian, let `ω` be a dualizing complex for `A`, put `P = A[x_1, …, x_n]` and write
`E = - ⊗_A^L P`.  Then the base-change morphism of [stacks 0E1X]

`RHom_A(K, ω) ⊗_A^L P ⟶ RHom_P(K ⊗_A^L P, ω ⊗_A^L P)`

is invertible for every `K` whose cohomology is finite in every degree.

The flat case of [stacks 0A6A] gives this for `K` pseudo-coherent, i.e. bounded above with finite
cohomology; the boundedness is removed by `Dualizing.isIso_app_of_isLE_tail`, the tails of the
truncation triangles being controlled by the finite injective dimension of `ω` and of
`ω ⊗_A^L P`. -/
theorem isIso_mvPolynomialDerivedHomBaseChange_of_finiteCohomology [IsNoetherianRing A] (n : ℕ)
    (ω K : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    IsIso (@Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u} A
      (MvPolynomial (Fin n) A) _ _ (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)
      (mvPolynomialExtension A n) (mvPolynomialExtensionFactors A n).hom
      (mvPolynomialExtension_isLeftDerivedFunctor A n) K ω) := by
  have hld := mvPolynomialExtension_isLeftDerivedFunctor A n
  let P := MvPolynomial (Fin n) A
  let f : A →+* P := MvPolynomial.C
  let Ef := mvPolynomialExtension A n
  have hflat : f.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  obtain ⟨aA, bA, IA, hIAge, hIAle, hIAinj, ⟨eIA⟩⟩ := hω.finiteInjectiveDimension
  have hωamp : StacksDraft.InjectiveDimension.HasInjectiveAmplitude ω aA bA :=
    ⟨IA, hIAge, hIAle, hIAinj, ⟨eIA⟩⟩
  have hωGE : ω.IsGE aA := DerivedCategory.TStructure.t.isGE_of_iso eIA.symm aA
  have hPω : IsDualizingComplex (Ef.obj ω) :=
    mvPolynomialBaseChange_isDualizingComplex n ω hω
  obtain ⟨aP, bP, IP, hIPge, hIPle, hIPinj, ⟨eIP⟩⟩ := hPω.finiteInjectiveDimension
  have hPωamp : StacksDraft.InjectiveDimension.HasInjectiveAmplitude (Ef.obj ω) aP bP :=
    ⟨IP, hIPge, hIPle, hIPinj, ⟨eIP⟩⟩
  let S : (DerivedCategory (ModuleCat.{u} A))ᵒᵖ ⥤
      (DerivedCategory (ModuleCat.{u} A))ᵒᵖ × DerivedCategory (ModuleCat.{u} A) :=
    Functor.prod' (𝟭 _) ((Functor.const _).obj ω)
  let F := S ⋙ Stacks.DerivedHom.ScalarTransportedInternalHom.hom A ⋙ Ef
  let G := S ⋙ Functor.prod Ef.op Ef ⋙
    Stacks.DerivedHom.ScalarTransportedInternalHom.hom P
  let α : F ⟶ G := Functor.whiskerLeft S
    (@Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeNatTrans.{u, u, u} A P _ _ f
      Ef (mvPolynomialExtensionFactors A n).hom (mvPolynomialExtension_isLeftDerivedFunctor A n))
  have hFtri : ∀ T : Triangle (DerivedCategory (ModuleCat.{u} A)), T ∈ distTriang _ →
      ∃ δ, Triangle.mk (F.map T.mor₂.op) (F.map T.mor₁.op) δ ∈
        distTriang (DerivedCategory (ModuleCat.{u} P)) := by
    intro T hT
    obtain ⟨δ, hδ⟩ := StacksDraft.Perfect.exists_distinguished_derivedHom_overRing A ω T hT
    let T' := Triangle.mk
      ((StacksDraft.Perfect.homFunctorOverRing A ω).map T.mor₂.op)
      ((StacksDraft.Perfect.homFunctorOverRing A ω).map T.mor₁.op) δ
    let T'' := Ef.mapTriangle.obj T'
    have hT'' : T'' ∈ distTriang _ := Ef.map_distinguished T' hδ
    refine ⟨T''.mor₃, ?_⟩
    change T'' ∈ distTriang _
    simpa [F, S, T', T''] using hT''
  have hGtri : ∀ T : Triangle (DerivedCategory (ModuleCat.{u} A)), T ∈ distTriang _ →
      ∃ δ, Triangle.mk (G.map T.mor₂.op) (G.map T.mor₁.op) δ ∈
        distTriang (DerivedCategory (ModuleCat.{u} P)) := by
    intro T hT
    let T' := Ef.mapTriangle.obj T
    have hT' : T' ∈ distTriang _ := Ef.map_distinguished T hT
    obtain ⟨δ, hδ⟩ := StacksDraft.Perfect.exists_distinguished_derivedHom_overRing P
      (Ef.obj ω) T' hT'
    simpa [G, S, T'] using ⟨δ, hδ⟩
  have hα : ∀ m : ℤ, IsIso (α.app (Opposite.op
      ((DerivedCategory.TStructure.t.truncLE m).obj K))) := by
    intro m
    have hpc : StacksDraft.PseudoCoherence.IsPseudoCoherent
        ((DerivedCategory.TStructure.t.truncLE m).obj K) :=
      isPseudoCoherent_truncLEObj K hK m
    have hbc := Stacks.DerivedHom.BaseChangeIso.isIso_derivedHomBaseChange.{u, u, u} f
      Ef (mvPolynomialExtensionFactors A n).hom
      ((DerivedCategory.TStructure.t.truncLE m).obj K) ω
      (Or.inr (Or.inr (Or.inl ⟨hflat, hpc, aA, hωGE⟩)))
    exact hbc
  have hF : ∃ c : ℤ, ∀ m : ℤ, (F.obj (Opposite.op
      ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K))).IsLE (c - m - 1) := by
    refine ⟨bA, fun m => ?_⟩
    have := dualizingDerivedHom_isLE_sub_sub A ω
      ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K) m aA bA inferInstance hωamp
    exact mapDerivedCategory_isLE (ModuleCat.extendScalars.{u, u, u} f)
      ((dualizingDerivedHomFunctor.{u, u} A ω).obj (Opposite.op
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K))) (bA - m - 1)
  have hG : ∃ c : ℤ, ∀ m : ℤ, (G.obj (Opposite.op
      ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K))).IsLE (c - m - 1) := by
    refine ⟨bP, fun m => ?_⟩
    exact dualizingDerivedHom_isLE_sub_sub P (Ef.obj ω) _ m aP bP
      (mapDerivedCategory_isGE (ModuleCat.extendScalars.{u, u, u} f)
        ((DerivedCategory.TStructure.t.truncGE (m + 1)).obj K) (m + 1)) hPωamp
  exact isIso_app_of_isLE_tail F G hFtri hGtri α K hα hF hG

/-! ### The comparison as a transformation of functors -/

/-- The base-change comparison
`RHom_A(-, ω) ⊗_A^L P ⟶ RHom_P(- ⊗_A^L P, ω ⊗_A^L P)`
of [stacks 0E1X] as a transformation of contravariant functors on all of `D(A)`, for
`P = A[x_1, …, x_n]`.  Naturality is
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_naturality` read with the identity in
the second variable. -/
def mvPolynomialDualityBaseChangeNatTrans (n : ℕ)
    (ω : DerivedCategory (ModuleCat.{u} A)) :
    dualizingDerivedHomFunctor.{u, u} A ω ⋙ mvPolynomialExtension A n ⟶
      (mvPolynomialExtension A n).op ⋙ dualizingDerivedHomFunctor.{u, u}
        (MvPolynomial (Fin n) A) ((mvPolynomialExtension A n).obj ω) where
  app X :=
    @Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{u, u, u} A
      (MvPolynomial (Fin n) A) _ _ (MvPolynomial.C : A →+* MvPolynomial (Fin n) A)
      (mvPolynomialExtension A n) (mvPolynomialExtensionFactors A n).hom
      (mvPolynomialExtension_isLeftDerivedFunctor A n) X.unop ω
  naturality {X Y} g := by
    have hld := mvPolynomialExtension_isLeftDerivedFunctor A n
    have h := Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange_naturality.{u, u, u}
      (MvPolynomial.C : A →+* MvPolynomial (Fin n) A) (mvPolynomialExtension A n)
      (mvPolynomialExtensionFactors A n).hom g.unop (𝟙 ω)
    rw [CategoryTheory.Functor.map_id] at h
    exact h

/-- **Flat base change of derived duality to a polynomial algebra, as an isomorphism of
functors.**  Let `A` be Noetherian, let `ω` be a dualizing complex for `A`, let
`P = A[x_1, …, x_n]` and let `X : J ⥤ D(A)` take values in `D_Coh(A)`.  Then

`RHom_A(X(-), ω) ⊗_A^L P ≅ RHom_P(X(-) ⊗_A^L P, ω ⊗_A^L P)`

as an isomorphism of functors `Jᵒᵖ ⥤ D(P)`.  Each component is invertible by
`Dualizing.isIso_mvPolynomialDerivedHomBaseChange_of_finiteCohomology`.

The statement is made along an arbitrary `X` rather than on the full subcategory `D_Coh(A)` so
that it can be read at the inclusion of `D_Coh(A)` and, equally, at a functor into `D_Coh(A)`
built from a presentation. -/
def mvPolynomialDualityBaseChangeNatIso [IsNoetherianRing A] (n : ℕ)
    {J : Type*} [Category J] (X : J ⥤ DerivedCategory (ModuleCat.{u} A))
    (hX : ∀ j : J, ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (X.obj j)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω) :
    X.op ⋙ dualizingDerivedHomFunctor.{u, u} A ω ⋙ mvPolynomialExtension A n ≅
      X.op ⋙ (mvPolynomialExtension A n).op ⋙ dualizingDerivedHomFunctor.{u, u}
        (MvPolynomial (Fin n) A) ((mvPolynomialExtension A n).obj ω) := by
  have happ : ∀ j : Jᵒᵖ, IsIso ((Functor.whiskerLeft X.op
      (mvPolynomialDualityBaseChangeNatTrans A n ω)).app j) := fun j =>
    isIso_mvPolynomialDerivedHomBaseChange_of_finiteCohomology A n ω (X.obj j.unop) hω
      (hX j.unop)
  have : IsIso (Functor.whiskerLeft X.op
      (mvPolynomialDualityBaseChangeNatTrans A n ω)) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (Functor.whiskerLeft X.op (mvPolynomialDualityBaseChangeNatTrans A n ω))

end Dualizing

end
