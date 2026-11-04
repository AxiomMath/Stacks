module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Restriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Representative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence of a direct summand on a ringed space

If a biproduct of two objects of the derived category of `𝒪_X`-modules is `m`-pseudo-coherent,
then so is each of its two summands, and likewise for pseudo-coherence without a fixed degree.

## Main results

* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_left_of_biprod` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_right_of_biprod` are the two assertions
  with a fixed degree.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherent_left_of_biprod` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherent_right_of_biprod` are the two unqualified
  assertions.

## Implementation notes

The argument is a descending induction on the degree, run against the two split distinguished
triangles `K ⟶ K ⊞ L ⟶ L` and `L ⟶ L ⊞ K ⟶ K` of the biproduct
(`CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished`). Part (1) of
[Stacks, Tag 08CD] turns `(m + 1)`-pseudo-coherence of one summand together with
`m`-pseudo-coherence of the biproduct into `m`-pseudo-coherence of the other summand, so once
both summands are known to be pseudo-coherent from *some* degree the bound descends one step at
a time to `m`.

That base case is where the hypothesis is used: locally the biproduct admits a strictly perfect
approximation, and a strictly perfect complex is bounded, so above the bound the cohomology of
the biproduct vanishes; the cohomology of each summand is a direct summand of it and therefore
vanishes too, which makes each summand pseudo-coherent from that degree
(`isPseudoCoherentFrom_of_homology_isZero`). Since the base case is only available locally, the
whole argument runs over an open subspace and is glued by
`isPseudoCoherentComplexFrom_of_local`.

## References

* [Stacks Project, Tag 08CE](https://stacks.math.columbia.edu/tag/08CE)
* [Stacks Project, Tag 08CD](https://stacks.math.columbia.edu/tag/08CD)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open StrictlyPerfect

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- A strictly perfect approximation defined on the whole of a ringed space makes the
approximated complex `m`-pseudo-coherent: restriction to the top open subspace is exact and
additive, so it carries the approximation to one of the shape the definition asks for. -/
private theorem isPseudoCoherentComplexFrom_of_approx {Y : RingedSpace.{u, u}}
    {P C : CochainComplex (OXMod.{u, u} Y) ℤ} (m : ℤ)
    (hP : IsStrictlyPerfect P) (α : P ⟶ C)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    IsPseudoCoherentComplexFrom C m := by
  have : PreservesFiniteLimits (restrictModules Y ⊤) :=
    restrictModules_preservesFiniteLimits Y ⊤
  have : PreservesFiniteColimits (restrictModules Y ⊤) :=
    restrictModules_preservesFiniteColimits Y ⊤
  exact fun _ => ⟨⊤, trivial, restrictComplex P ⊤, isStrictlyPerfect_restrictComplex hP ⊤,
    ((restrictModules Y ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map α,
    fun j hj => isIso_homologyMap_map _ α j (hiso j hj),
    epi_homologyMap_map _ α m hepi⟩

/-- A complex of `𝒪_X`-modules whose restriction to each member of an open cover of `X` is
`m`-pseudo-coherent is itself `m`-pseudo-coherent: an approximation over an open subspace of an
open subspace of `X` transports, along the nested identification, to one over the corresponding
open subspace of `X`. -/
private theorem isPseudoCoherentComplexFrom_of_local
    (C : CochainComplex (OXMod.{u, u} X) ℤ) (m : ℤ)
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      IsPseudoCoherentComplexFrom (restrictComplex C U) m) :
    IsPseudoCoherentComplexFrom C m := by
  intro x
  obtain ⟨U, hxU, hU⟩ := h x
  obtain ⟨V, hxV, P, hP, α, hiso, hepi⟩ := hU ⟨x, hxU⟩
  let F := (nestedModulesEquivalence U V).functor
  have : F.Additive := nestedModulesEquivalence_functor_additive U V
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  refine ⟨U.isOpenEmbedding.functor.obj V, ⟨⟨x, hxU⟩, hxV, rfl⟩,
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    isStrictlyPerfect_nestedModulesEquivalence U V P hP,
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ (nestedComplexIso U V C).hom, ?_, ?_⟩
  · intro j hj
    rw [HomologicalComplex.homologyMap_comp]
    have := isIso_homologyMap_map F α j (hiso j hj)
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    have := epi_homologyMap_map F α m hepi
    infer_instance

open scoped ZeroObject in
/-- A complex of `𝒪_X`-modules whose cohomology vanishes in every degree at least `n` is
`n`-pseudo-coherent: the zero complex is strictly perfect and approximates it, both sides of the
zero morphism having vanishing cohomology in those degrees. -/
private theorem isPseudoCoherentComplexFrom_of_homology_isZero {Y : RingedSpace.{u, u}}
    (C : CochainComplex (OXMod.{u, u} Y) ℤ) (n : ℤ)
    (hC : ∀ j : ℤ, n ≤ j → IsZero (HomologicalComplex.homology C j)) :
    IsPseudoCoherentComplexFrom C n := by
  have hzero (j : ℤ) : IsZero ((0 : CochainComplex (OXMod.{u, u} Y) ℤ).X j) :=
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) j).map_isZero (isZero_zero _)
  have hsrc (j : ℤ) :
      IsZero (HomologicalComplex.homology (0 : CochainComplex (OXMod.{u, u} Y) ℤ) j) :=
    (((0 : CochainComplex (OXMod.{u, u} Y) ℤ)).sc j).isZero_homology_of_isZero_X₂ (hzero j)
  have hiso (j : ℤ) (hj : n ≤ j) :
      IsIso (HomologicalComplex.homologyMap (0 : (0 : CochainComplex _ ℤ) ⟶ C) j) :=
    (hsrc j).isIso (hC j hj) _
  exact isPseudoCoherentComplexFrom_of_approx n
    (isStrictlyPerfect_of_forall_isZero hzero) 0
    (fun j hj => hiso j hj.le) (@IsIso.epi_of_iso _ _ _ _ _ (hiso n le_rfl))

/-- Cohomology of an object of the derived category vanishes in degree `j` exactly when that of
any complex representing it does. -/
private theorem isZero_homologyFunctor_iff {Y : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} Y)] {C : CochainComplex (OXMod.{u, u} Y) ℤ}
    {E : DerivedCategory (OXMod.{u, u} Y)} (e : DerivedCategory.Q.obj C ≅ E) (j : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).obj E) ↔
      IsZero (HomologicalComplex.homology C j) :=
  (((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).mapIso e).symm ≪≫
    (DerivedCategory.homologyFunctorFactors (OXMod.{u, u} Y) j).app C).isZero_iff

/-- An object of the derived category of `𝒪_X`-modules whose cohomology vanishes in every degree
at least `n` is `n`-pseudo-coherent. -/
private theorem isPseudoCoherentFrom_of_homology_isZero {Y : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} Y)]
    (E : DerivedCategory (OXMod.{u, u} Y)) (n : ℤ)
    (hE : ∀ j : ℤ, n ≤ j →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).obj E)) :
    IsPseudoCoherentFrom E n := by
  refine ⟨DerivedCategory.Q.objPreimage E,
    isPseudoCoherentComplexFrom_of_homology_isZero _ n fun j hj =>
    (isZero_homologyFunctor_iff (DerivedCategory.Q.objObjPreimageIso E) j).1 (hE j hj),
    ⟨DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-- Both summands of an `m`-pseudo-coherent biproduct are `m`-pseudo-coherent, provided both are
already known to be pseudo-coherent from some degree `N ≥ m`: part (1) of [Stacks, Tag 08CD],
applied to the two split triangles of the biproduct, lowers the bound on each summand by one
step, so a descending induction from `N` reaches `m`. -/
private theorem isPseudoCoherentFrom_biprod_of_high
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    {K L : DerivedCategory (OXMod.{u, u} X)} (m N : ℤ) (hmN : m ≤ N)
    (hK : IsPseudoCoherentFrom K N) (hL : IsPseudoCoherentFrom L N)
    (h : IsPseudoCoherentFrom (K ⊞ L) m) :
    IsPseudoCoherentFrom K m ∧ IsPseudoCoherentFrom L m := by
  have hsum (i : ℤ) (hi : m ≤ i) : IsPseudoCoherentFrom (K ⊞ L) i := h.mono hi
  refine Int.leInductionDown (m := N) (motive := fun i _ => m ≤ i →
    IsPseudoCoherentFrom K i ∧ IsPseudoCoherentFrom L i) (fun _ => ⟨hK, hL⟩)
    (fun i _ ih hmi => ?_) m hmN le_rfl
  have hs := hsum (i - 1) (by omega)
  have hKi : IsPseudoCoherentFrom K (i - 1 + 1) := by
    simpa only [sub_add_cancel] using (ih (by omega)).1
  have hLi : IsPseudoCoherentFrom L (i - 1 + 1) := by
    simpa only [sub_add_cancel] using (ih (by omega)).2
  exact ⟨isPseudoCoherentFrom_obj₃_of_distinguished (i - 1) (binaryBiproductTriangle L K)
      (binaryBiproductTriangle_distinguished L K) hLi
      (hs.of_iso (biprod.braiding K L)),
    isPseudoCoherentFrom_obj₃_of_distinguished (i - 1) (binaryBiproductTriangle K L)
      (binaryBiproductTriangle_distinguished K L) hKi hs⟩

/-- **Stacks Project, Tag 08CE.** The first summand of an `m`-pseudo-coherent biproduct is
`m`-pseudo-coherent. -/
@[stacks 08CE "m-pseudo-coherent, first summand", sga "6 I 2.12" "n-pc: sum ⇒ F'"]
public theorem isPseudoCoherentFrom_left_of_biprod
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K L : DerivedCategory (OXMod.{u, u} X)) (m : ℤ)
    (h : IsPseudoCoherentFrom (K ⊞ L) m) : IsPseudoCoherentFrom K m := by
  let _ : ∀ W : Opens X.carrier,
      HasDerivedCategory.{max u (u + 1)} (OXMod.{u, u} (X.restrict W.isOpenEmbedding)) :=
    fun _ => HasDerivedCategory.standard _
  let A := DerivedCategory.Q.objPreimage K
  let B := DerivedCategory.Q.objPreimage L
  let eA := DerivedCategory.Q.objObjPreimageIso K
  let eB := DerivedCategory.Q.objObjPreimageIso L
  have : PreservesBinaryBiproducts (DerivedCategory.Q (C := OXMod.{u, u} X)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let eS : DerivedCategory.Q.obj (A ⊞ B) ≅ K ⊞ L :=
    DerivedCategory.Q.mapBiprod A B ≪≫ biprod.mapIso eA eB
  have hS := isPseudoCoherentComplexFrom_of_iso (K ⊞ L) m h (A ⊞ B) eS
  refine ⟨A, isPseudoCoherentComplexFrom_of_local A m fun x => ?_, ⟨eA⟩⟩
  obtain ⟨U, hxU, P, hP, α, hα, hepi⟩ := hS x
  let Rc := (restrictModules X U).mapHomologicalComplex (ComplexShape.up ℤ)
  have : PreservesBinaryBiproducts Rc := preservesBinaryBiproducts_of_preservesBiproducts _
  have : PreservesBinaryBiproducts
      (DerivedCategory.Q (C := OXMod.{u, u} (X.restrict U.isOpenEmbedding))) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let eSU : restrictComplex (A ⊞ B) U ≅ restrictComplex A U ⊞ restrictComplex B U :=
    Rc.mapBiprod A B
  let M := DerivedCategory.Q.obj (restrictComplex A U)
  let N := DerivedCategory.Q.obj (restrictComplex B U)
  let eU : DerivedCategory.Q.obj (restrictComplex (A ⊞ B) U) ≅ M ⊞ N :=
    DerivedCategory.Q.mapIso eSU ≪≫
      DerivedCategory.Q.mapBiprod (restrictComplex A U) (restrictComplex B U)
  have hsum : IsPseudoCoherentFrom (M ⊞ N) m :=
    ((isPseudoCoherentComplexFrom_of_approx m hP α hα hepi).isPseudoCoherentFrom_Q).of_iso eU
  obtain ⟨b, hb⟩ := hP.bounded.bddAbove
  have hzero (j : ℤ) (hj : max m b + 1 ≤ j) :
      IsZero ((DerivedCategory.homologyFunctor
        (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) j).obj (M ⊞ N)) := by
    have hPj : IsZero (P.X j) := by
      by_contra hn
      have hjb : j ≤ b := hb hn
      omega
    have hHj : IsZero (HomologicalComplex.homology P j) :=
      (P.sc j).isZero_homology_of_isZero_X₂ hPj
    have : IsIso (HomologicalComplex.homologyMap α j) := hα j (by omega)
    have hSU : IsZero (HomologicalComplex.homology (restrictComplex (A ⊞ B) U) j) :=
      hHj.of_epi (HomologicalComplex.homologyMap α j)
    exact (isZero_homologyFunctor_iff eU j).2 hSU
  have hsplit {T : DerivedCategory (OXMod.{u, u} (X.restrict U.isOpenEmbedding))}
      (f : T ⟶ M ⊞ N) [IsSplitMono f] : IsPseudoCoherentFrom T (max m b + 1) :=
    isPseudoCoherentFrom_of_homology_isZero T _ fun j hj =>
      (hzero j hj).of_mono ((DerivedCategory.homologyFunctor _ j).map f)
  have hM' := (isPseudoCoherentFrom_biprod_of_high m (max m b + 1) (by omega)
    (hsplit biprod.inl) (hsplit biprod.inr) hsum).1
  exact ⟨U, hxU, isPseudoCoherentComplexFrom_of_iso M m hM' (restrictComplex A U) (Iso.refl _)⟩

/-- **Stacks Project, Tag 08CE.** The second summand of an `m`-pseudo-coherent biproduct is
`m`-pseudo-coherent. -/
@[stacks 08CE "m-pseudo-coherent, second summand", sga "6 I 2.12" "n-pc: sum ⇒ F''"]
public theorem isPseudoCoherentFrom_right_of_biprod
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K L : DerivedCategory (OXMod.{u, u} X)) (m : ℤ)
    (h : IsPseudoCoherentFrom (K ⊞ L) m) : IsPseudoCoherentFrom L m :=
  isPseudoCoherentFrom_left_of_biprod L K m (h.of_iso (biprod.braiding K L))

/-- **Stacks Project, Tag 08CE.** The first summand of a pseudo-coherent biproduct is
pseudo-coherent. -/
@[stacks 08CE "pseudo-coherent, first summand"]
public theorem isPseudoCoherent_left_of_biprod
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K L : DerivedCategory (OXMod.{u, u} X)) (h : IsPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent K := by
  obtain ⟨E, hE, ⟨e⟩⟩ := h
  refine ⟨DerivedCategory.Q.objPreimage K, fun m => ?_,
    ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  exact isPseudoCoherentComplexFrom_of_iso K m
    (isPseudoCoherentFrom_left_of_biprod K L m ⟨E, hE m, ⟨e⟩⟩) _
    (DerivedCategory.Q.objObjPreimageIso K)

/-- **Stacks Project, Tag 08CE.** The second summand of a pseudo-coherent biproduct is
pseudo-coherent. -/
@[stacks 08CE "pseudo-coherent, second summand"]
public theorem isPseudoCoherent_right_of_biprod
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (K L : DerivedCategory (OXMod.{u, u} X)) (h : IsPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent L :=
  isPseudoCoherent_left_of_biprod L K (h.of_iso (biprod.braiding K L))

end AlgebraicGeometry.RingedSpace

end
