module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeFieldExtension
public import StacksFrontier.AlgebraicGeometry.Curves.NodalUnramifiedArbitraryField
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedGaloisFixed
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct

/-!
# The depth and Fitting-ideal criterion for a node over an arbitrary base field

Let `k` be a field, let `X` be a one-dimensional scheme locally of finite type over `k` and let
`x` be a closed point of `X`.  If `κ(x)/k` is separable, `𝒪_{X,x}` has depth one and the first
Fitting ideal of `Ω_{X/k}` generates the maximal ideal of `𝒪_{X,x}`, then `x` is a node.  This is
the implication (5) ⟹ (1) of Stacks Tag 0C4D over an arbitrary base field; over an algebraically
closed field it is
`Stacks.Curves.isNode_of_depth_eq_one_and_stalk_fittingIdeal_eq_maximalIdeal_of_isAlgClosed`.

## Main results

* `Stacks.Curves.isField_localization_atPrime_tensorProduct` — a localization of `L ⊗_k K` at a
  prime is a field, for `L/k` finite separable and `K/k` arbitrary.
* `Stacks.Curves.depth_quotient_maximalIdeal_eq_zero` — the residue field of a Noetherian local
  ring has depth zero.
* `Stacks.Curves.map_maximalIdeal_stalk_baseChange_of_isSeparable` — at a point of the base
  change of `X` to a field extension above a closed point `x` with `κ(x)/k` separable, the
  maximal ideal of `𝒪_{X,x}` generates the maximal ideal upstairs.
* `Stacks.Curves.isNode_of_depth_eq_one_and_stalk_fittingIdeal_eq_maximalIdeal` — the implication
  (5) ⟹ (1) of Tag 0C4D over an arbitrary base field.

## Implementation notes

The argument is base change to the algebraic closure `k̄`, where the implication is available, and
descent of the node condition by Tag 0C56 (`Stacks.Curves.isNode_iff_of_fieldExtension`), which
needs the dimension hypothesis the algebraically closed case does without.

What has to be checked is that the three clauses of condition (5) rise to a point `x̄` of `X_{k̄}`
above `x`.  Separability of `κ(x̄)/k̄` is free, `k̄` being perfect.  The other two both follow once
the closed fibre of `𝒪_{X,x} ⟶ 𝒪_{X_{k̄},x̄}` is a field, that is, once `𝔪_x` generates `𝔪_{x̄}`:
the Fitting-ideal clause because formation of the Fitting ideal commutes with base change
(`AlgebraicGeometry.stalk_fittingIdeal_relativeDifferentials_of_isPullback`), so the stalk
upstairs is `𝔪_x · 𝒪_{X_{k̄},x̄}`; and the depth clause because depth is additive along a flat
local homomorphism (Tag 0337), the fibre contributing zero.

That the closed fibre is a field is where separability of `κ(x)/k` enters, and it is the one
place where it is used.  By Tag 0C4Y (`AlgebraicGeometry.specialFibreRingEquiv`) the closed fibre
is a localization of `κ(x) ⊗_k k̄`, which is reduced because `κ(x)/k` is separable, hence
geometrically reduced, and Artinian because `κ(x)/k` is finite — the point is closed.  A
localization of a reduced Artinian ring at a prime is a field: its maximal ideal is its
nilradical, which is zero.

Both reducedness and Artinianness are transported across
`Algebra.TensorProduct.comm`: the tensor-reducedness instance (Tag 034N) asks for the
*second* factor to be geometrically reduced, and the finiteness of `κ(x) ⊗_k k̄` over `k̄` is
`Module.Finite.base_change` with `k̄` on the left.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C4Y](https://stacks.math.columbia.edu/tag/0C4Y)
* [Stacks Project, Tag 0C56](https://stacks.math.columbia.edu/tag/0C56)
* [Stacks Project, Tag 0337](https://stacks.math.columbia.edu/tag/0337)
* [Stacks Project, Tag 034N](https://stacks.math.columbia.edu/tag/034N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry IsLocalRing
open scoped TensorProduct

universe u

namespace Stacks.Curves

/-! ### Localizations of `L ⊗_k K` for `L/k` finite separable -/

/-- **A localization of `L ⊗_k K` at a prime is a field**, for `L/k` a finite separable extension
and `K/k` an arbitrary one.  The ring `L ⊗_k K` is reduced, `L/k` being separable hence
geometrically reduced, and Artinian, `L/k` being finite; so the maximal ideal of a localization
is its nilradical, which is zero. -/
theorem isField_localization_atPrime_tensorProduct (k L K : Type u) [Field k] [Field L] [Field K]
    [Algebra k L] [Algebra k K] [Module.Finite k L] [Algebra.IsSeparable k L]
    (P : Ideal (L ⊗[k] K)) [P.IsPrime] : IsField (Localization.AtPrime P) := by
  have : Algebra.IsGeometricallyReduced k L := Algebra.IsGeometricallyReduced.of_isSeparable k L
  have : Module.Finite K (K ⊗[k] L) := Module.Finite.base_change k K L
  have : IsArtinianRing (K ⊗[k] L) := isArtinian_of_tower K inferInstance
  have : IsArtinianRing (L ⊗[k] K) :=
    (Algebra.TensorProduct.comm k K L).toRingEquiv.isArtinianRing
  have : IsReduced (L ⊗[k] K) :=
    isReduced_of_ringEquiv (Algebra.TensorProduct.comm k L K).toRingEquiv inferInstance
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Ring.KrullDimLE.nilradical_eq_maximalIdeal]
  simp

/-! ### The depth of a residue field -/

/-- **The residue field of a Noetherian local ring has depth zero** over the maximal ideal: the
support of the module is a point, so its depth is at most zero. -/
theorem depth_quotient_maximalIdeal_eq_zero (S : Type u) [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] :
    Module.depth S (maximalIdeal S) (S ⧸ maximalIdeal S) = 0 := by
  have hfield : IsField (S ⧸ maximalIdeal S) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp (maximalIdeal.isMaximal S)
  have hbot : (maximalIdeal S) • (⊤ : Submodule S (S ⧸ maximalIdeal S)) = ⊥ := by
    refine le_antisymm (Submodule.smul_le.mpr fun r hr m _ => ?_) bot_le
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [Submodule.mem_bot, Algebra.smul_def]
    simp only [Ideal.Quotient.algebraMap_eq, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mul_mem_right _ _ hr)
  have hne : (maximalIdeal S) • (⊤ : Submodule S (S ⧸ maximalIdeal S)) ≠ ⊤ := by
    rw [hbot]
    refine fun h => hfield.exists_pair_ne.choose_spec.choose_spec ?_
    have h1 := (Submodule.eq_bot_iff _).mp h.symm
    exact (h1 _ Submodule.mem_top).trans (h1 _ Submodule.mem_top).symm
  have hle := Module.depth_le_supportDim S (maximalIdeal S) (S ⧸ maximalIdeal S) hne
  rw [Module.supportDim_quotient_eq_ringKrullDim,
    ringKrullDim_eq_zero_of_isField hfield] at hle
  exact le_antisymm (by exact_mod_cast hle) zero_le

/-! ### The closed fibre of the base change at a closed point with separable residue field -/

/-- **At a point of the base change of `X` to a field extension lying above a closed point `x` at
which `κ(x)/k` is separable, the maximal ideal of `𝒪_{X,x}` generates the maximal ideal of the
local ring upstairs.**

By Tag 0C4Y the closed fibre of `𝒪_{X,x} ⟶ 𝒪_{X_K,y}` is a localization of `κ(x) ⊗_k K`, which is
reduced and Artinian here, so that localization is a field. -/
theorem map_maximalIdeal_stalk_baseChange_of_isSeparable (k K : Type u) [Field k] [Field K]
    [Algebra k K] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hx : IsClosed ({(pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y} : Set X))
    (hsep :
      letI : Algebra k (X.residueField ((pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y)) :=
        (fieldToResidue f ((pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y)).hom.toAlgebra
      Algebra.IsSeparable k (X.residueField ((pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y))) :
    Ideal.map ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom
        (maximalIdeal (X.presheaf.stalk ((pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y))) =
      maximalIdeal ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))
        : Scheme.{u}).presheaf.stalk y) := by
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (pullback f g : Scheme.{u})
  let F : Y ⟶ X := pullback.fst f g
  let x := F.base y
  -- the two `k`-algebra structures on `κ(x)` agree
  let : (f.base x).asIdeal.IsPrime := (f.base x).isPrime
  let algResidue : Algebra k (X.residueField x) :=
    ((CommRingCat.ofHom (algebraMap k (f.base x).asIdeal.ResidueField)) ≫
      (Scheme.Spec.residueFieldIso (.of k) (f.base x)).inv ≫
      f.residueFieldMap x).hom.toAlgebra
  have heqmap : ((CommRingCat.ofHom (algebraMap k (f.base x).asIdeal.ResidueField)) ≫
      (Scheme.Spec.residueFieldIso (.of k) (f.base x)).inv ≫ f.residueFieldMap x) =
      fieldToResidue f x := (fieldToResidue_eq k X f x).symm
  have hinst : algResidue = (fieldToResidue f x).hom.toAlgebra := by
    rw [show algResidue = ((CommRingCat.ofHom
        (algebraMap k (f.base x).asIdeal.ResidueField)) ≫
      (Scheme.Spec.residueFieldIso (.of k) (f.base x)).inv ≫
      f.residueFieldMap x).hom.toAlgebra from rfl, heqmap]
  have hsep' : @Algebra.IsSeparable k (X.residueField x) _ _ algResidue := by
    rw [hinst]; exact hsep
  have hfin : @Module.Finite k (X.residueField x) _ _ algResidue.toModule := by
    rw [hinst]; exact module_finite_fieldToResidue f x hx
  -- the closed fibre is a localization of `κ(x) ⊗[k] K`, hence a field
  obtain ⟨e⟩ := nonempty_pullbackPointTensorRingEquiv k K X f y
  have hpprime : (RingHom.ker (Scheme.Pullback.ofPointTensor y).hom).IsPrime :=
    RingHom.ker_isPrime _
  have hPprime : (Ideal.comap e.symm.toRingHom
      (RingHom.ker (Scheme.Pullback.ofPointTensor y).hom)).IsPrime := Ideal.comap_isPrime _ _
  have hPloc : Localization.AtPrime (Ideal.comap e.symm.toRingHom
        (RingHom.ker (Scheme.Pullback.ofPointTensor y).hom)) ≃+*
      Localization.AtPrime (RingHom.ker (Scheme.Pullback.ofPointTensor y).hom) :=
    Localization.localRingEquiv _ _ e.symm rfl
  have hfieldP : IsField (Localization.AtPrime (Ideal.comap e.symm.toRingHom
      (RingHom.ker (Scheme.Pullback.ofPointTensor y).hom))) :=
    isField_localization_atPrime_tensorProduct k (X.residueField x) K _
  have hfieldFibre : IsField (Y.presheaf.stalk y ⧸
      Ideal.map (F.stalkMap y).hom (maximalIdeal (X.presheaf.stalk x))) :=
    (specialFibreRingEquiv k K f y).isField (hPloc.symm.isField hfieldP)
  -- a maximal ideal inside the maximal ideal is it
  have hmax : (Ideal.map (F.stalkMap y).hom (maximalIdeal (X.presheaf.stalk x))).IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hfieldFibre
  refine hmax.eq_of_le (maximalIdeal.isMaximal _).ne_top ?_
  rw [Ideal.map_le_iff_le_comap]
  exact le_of_eq (IsLocalRing.maximalIdeal_comap (F.stalkMap y).hom).symm

/-! ### The implication (5) ⟹ (1) of Tag 0C4D over an arbitrary base field -/

/-- **The implication (5) ⟹ (1) of Stacks Tag 0C4D over an arbitrary base field.**

Let `k` be a field, `X` a one-dimensional scheme locally of finite type over `k` and `x` a closed
point of `X`.  If the residue field extension `κ(x)/k` is separable, the local ring `𝒪_{X,x}` has
depth one and the first Fitting ideal of `Ω_{X/k}` generates the maximal ideal of `𝒪_{X,x}`, then
`x` is a node.

The three clauses of the hypothesis are exactly condition (5) of the tag, in the spelling used by
`Stacks.Curves.isNode_tfae_of_residual_equivalences`, and the conclusion is its condition (1).
Unlike the algebraically closed case the dimension hypothesis of the tag is used, through Tag
0C56. -/
theorem isNode_of_depth_eq_one_and_stalk_fittingIdeal_eq_maximalIdeal
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra k (X.residueField x) :=
      (fieldToResidue (X ↘ Spec (.of k)) x).hom.toAlgebra
    Algebra.IsSeparable k (X.residueField x) →
      Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
          (X.presheaf.stalk x) = 1 →
        IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials
            (X ↘ Spec (.of k))) (1 : ℤ)) x =
            maximalIdeal (X.presheaf.stalk x) →
          IsNode k X x := by
  let : Algebra k (X.residueField x) := (fieldToResidue (X ↘ Spec (.of k)) x).hom.toAlgebra
  intro hsep hdepth hfit
  set f : X ⟶ Spec (.of k) := X ↘ Spec (.of k) with hf
  let K := AlgebraicClosure k
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (pullback f g : Scheme.{u})
  let F : Y ⟶ X := pullback.fst f g
  let q : Y ⟶ Spec (.of K) := pullback.snd f g
  let instY : Y.Over (Spec (.of K)) := ⟨q⟩
  have hlft : LocallyOfFiniteType (Y ↘ Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f g))
  -- a point of the base change above `x`
  obtain ⟨xbar, hxbar⟩ : ∃ y, F.base y = x := surjective_baseChange_fst k K f x
  subst hxbar
  have hxbarcl : IsClosed ({xbar} : Set Y) :=
    isClosed_singleton_baseChange_of_isClosed k K X f xbar hx
  -- the maximal ideal downstairs generates the one upstairs
  have hmapm : Ideal.map (F.stalkMap xbar).hom
      (maximalIdeal (X.presheaf.stalk (F.base xbar))) =
      maximalIdeal (Y.presheaf.stalk xbar) :=
    map_maximalIdeal_stalk_baseChange_of_isSeparable k K X f xbar hx hsep
  -- the Fitting-ideal clause rises
  have hsq : IsPullback F q f g := IsPullback.of_hasPullback f g
  have hq : (Y ↘ Spec (.of K)) = q := rfl
  have hbc := stalk_fittingIdeal_relativeDifferentials_of_isPullback F q f g hsq 1 xbar
  rw [← hq] at hbc
  have hfitbar : IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials
      (Y ↘ Spec (.of K))) (1 : ℤ)) xbar = maximalIdeal (Y.presheaf.stalk xbar) := by
    rw [hbc, hfit]
    exact hmapm
  -- the depth clause rises, the closed fibre being the residue field
  have hgflat : Flat g := (Flat.SpecMap_iff).2
    (RingHom.Flat.of_isField (Field.toIsField k) (algebraMap k K))
  have hFflat : Flat F := inferInstanceAs (Flat (pullback.fst f g))
  have hlocal : IsLocalHom (F.stalkMap xbar).hom := F.toLRSHom.prop xbar
  have hnoethY : IsNoetherianRing (Y.presheaf.stalk xbar) :=
    (isNagataRing_stalk_of_locallyOfFiniteType K (Y ↘ Spec (.of K)) xbar).isNoetherianRing
  have hdepthbar : Module.depth (Y.presheaf.stalk xbar) (maximalIdeal (Y.presheaf.stalk xbar))
      (Y.presheaf.stalk xbar) = 1 := by
    algebraize [(F.stalkMap xbar).hom]
    have : Module.Flat (X.presheaf.stalk (F.base xbar)) (Y.presheaf.stalk xbar) :=
      Flat.stalkMap F xbar
    have : IsLocalHom
        (algebraMap (X.presheaf.stalk (F.base xbar)) (Y.presheaf.stalk xbar)) := hlocal
    rw [Module.depth_self_eq_depth_self_add_depth_quotient_map_maximalIdeal
      (X.presheaf.stalk (F.base xbar)) (Y.presheaf.stalk xbar),
      show (Ideal.map (algebraMap (X.presheaf.stalk (F.base xbar)) (Y.presheaf.stalk xbar))
        (maximalIdeal (X.presheaf.stalk (F.base xbar)))) =
          maximalIdeal (Y.presheaf.stalk xbar) from hmapm,
      depth_quotient_maximalIdeal_eq_zero (Y.presheaf.stalk xbar), add_zero]
    exact hdepth
  -- condition (5) holds upstairs, where the implication is available
  let algBK : Algebra K (Y.presheaf.stalk xbar) :=
    (((Scheme.ΓSpecIso (.of K)).inv ≫ (Y ↘ Spec (.of K)).appTop ≫
      Y.presheaf.germ ⊤ xbar trivial).hom).toAlgebra
  let : Algebra K (Y.residueField xbar) :=
    ((Y.residue xbar).hom.comp (((Scheme.ΓSpecIso (.of K)).inv ≫
      (Y ↘ Spec (.of K)).appTop ≫ Y.presheaf.germ ⊤ xbar trivial).hom)).toAlgebra
  have hnodeY : IsNode K Y xbar :=
    isNode_of_depth_eq_one_and_stalk_fittingIdeal_eq_maximalIdeal_of_isAlgClosed K Y xbar
      hxbarcl (Algebra.isSeparableExtension_of_perfectField K (Y.residueField xbar))
      hdepthbar hfitbar
  -- and the node condition descends by Tag 0C56
  exact (isNode_iff_of_fieldExtension k K X f hdim (F.base xbar) xbar rfl).mpr hnodeY

end Stacks.Curves

end
