module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerTopBasis
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBifunctorStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
import StacksCore.Tactic.StacksAttribute

/-!
# The determinant comparison of a short exact sequence is an isomorphism

Let `(X, O_X)` be a ringed space and let `0 → E' → E → E'' → 0` be a short exact sequence of
sheaves of `O_X`-modules with `E'` finite locally free of constant rank `r'` and `E''` finite
locally free of constant rank `k + 1`. The canonical comparison

`⋀^{r'}(E') ⊗ ⋀^{k+1}(E'') ⟶ ⋀^{r' + k + 1}(E)`

of `Stacks.SheafOfModules.TopWedge.detComparison` is then an **isomorphism**. This is the
remaining clause of [Stacks, Tag 0B38] in the constant-rank form. Read through the
identification `⋀ʳ F ≅ det(F)` of [Stacks, Tag 0B37] it becomes the isomorphism
`det(E') ⊗ det(E'') ≅ det(E)` of the source, which is
`Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantIso` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorDeterminantShortExactIso`.

## Main definitions

* `Stacks.SheafOfModules.TopWedge.stalkBasis`: an ordered basis of the stalk of a sheaf of
  modules which is finite locally free of constant rank.
* `Stacks.SheafOfModules.TopWedge.stalkExteriorPowerTopBasis` and
  `Stacks.SheafOfModules.TopWedge.stalkTensorTopBasis`: the rank-one bases of the stalks of the
  target and of the source of the comparison.

## Main results

* `Stacks.SheafOfModules.TopWedge.isIso_detComparison`: **the comparison is an isomorphism.**
* `Stacks.SheafOfModules.TopWedge.surjective_stalkMapL_detComparison`: it is surjective on
  stalks, which is the whole content.
* `Stacks.SheafOfModules.TopWedge.exists_basis_append_stalk`: an ordered basis of the middle
  stalk whose first `r'` members are the images of a basis of `E'_x`, together with the
  generation of the top exterior power by the corresponding wedge.
* `Stacks.SheafOfModules.TopWedge.stalkMapL_shortExact`: the stalk of a short exact sequence of
  sheaves of modules is short exact, in the linear-map spelling the argument uses.

## Implementation notes

**The shape of the argument.** Isomorphy is stalkwise
(`AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap`), and at a point `x` the stalk
sequence `0 → E'_x → E_x → E''_x → 0` is short exact with both ends free, of ranks `r'` and
`k + 1`. So `E''_x` is projective, the sequence splits by some retraction `σ`, and
`Stacks.ExteriorPower.exists_basis_append` assembles an ordered basis of `E_x` whose first `r'`
members are the images of a basis `b'` of `E'_x` and whose last `k + 1` members are
`σ(b''_j)`. The wedge of an ordered basis generates the top exterior power
(`Stacks.ExteriorPower.span_ιMulti_eq_top`), and the wedge-and-lift formula
`Stacks.SheafOfModules.TopWedge.detComparison_wedge` exhibits exactly that wedge in the image of
the stalk map, once the finitely many germs involved are realised by sections over a single
neighbourhood. That gives **surjectivity**.

Injectivity is then free: source and target are both free of rank one over the stalk ring — the
target by the basis just constructed, the source because the stalk of a tensor product is the
tensor product of the stalks ([Stacks, Tag 01CB], `PresheafOfModules.tensorSheafStalkEquiv`) and
a tensor product of two rank-one free modules is free of rank one — and a surjection between
free modules of rank one over a commutative ring is injective, by the Orzech property
(`Stacks.ExteriorPower.injective_of_surjective_of_basis_fin_one`).

**No hypothesis on `E` is needed.** [Stacks, Tag 0B38] assumes all three of `E'`, `E` and `E''`
finite locally free; the argument above derives the freeness of the stalks of `E` from the other
two and the splitting, so the statements below carry no hypothesis on `E`. That is a
strengthening, not a weakening.

**Why the hypotheses on `E''` and on `f` cannot be dropped.** They are both part of the Stacks
statement, and the conclusion is false without the first: see the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact`, which exhibit a
sequence over a discrete valuation ring with `E'` free of rank one, `E` free of rank two and
`f` injective, for which the comparison is not even an epimorphism.

**Two spellings of the stalk ring.** `AlgebraicGeometry.SheafOfModules.stalkMap` is linear over
the stalk of the sheaf of rings taken in `RingCat`, while the exterior- and tensor-power stalk
comparisons are linear over the stalk taken in `CommRingCat`. These are different objects, so
the module-theoretic part of the argument is carried out with `PresheafOfModules.stalkMapL`,
which is linear over the second, and `stalkMap_hom_apply` records that the two have the same
underlying function.

**Why the argument is cut into so many declarations.** Every mention of a stalk comparison or of
`PresheafOfModules.stalkMapL` makes the elaborator re-solve the module structure on a stalk, and
unify a functor composition against `CategoryTheory.Sheaf.toRingCat`. Each such step is
affordable and a handful of them is not: putting the exactness of the stalk sequence and the
construction of the appended basis in one declaration exhausts the heartbeat budget, although
either half alone is comfortable. The facts are therefore passed between declarations as
explicit hypotheses, and `exists_exteriorPowerStalkEquiv_wedgeSec` bundles the comparison of
Tag 01CH with the only property of it that is used, so that it is elaborated once.

## References

* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules.TopWedge

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-! ### Two spellings of the stalk map -/

/-- The stalk map of a morphism of sheaves of modules, read as a linear map over the stalk of
the sheaf of commutative rings, has the same underlying function as
`AlgebraicGeometry.SheafOfModules.stalkMap`. Both are the map induced on abelian-group stalks
by the underlying morphism of presheaves. -/
theorem stalkMap_hom_apply
    {M N : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (φ : M ⟶ N) (x : ↥X) (z : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    (AlgebraicGeometry.SheafOfModules.stalkMap
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x φ).hom z =
      PresheafOfModules.stalkMapL x φ.val z := rfl

/-! ### Realising finitely many germs over one neighbourhood -/

/-- Finitely many germs of two sheaves of modules at a point are realised by sections over a
single neighbourhood of that point. -/
theorem exists_common_germ
    (M N : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    (x : ↥X) {r m : ℕ} (v : Fin r → ↑(TopCat.Presheaf.stalk M.val.presheaf x))
    (w : Fin m → ↑(TopCat.Presheaf.stalk N.val.presheaf x)) :
    ∃ (W : Opens ↥X) (hxW : x ∈ W) (s : Fin r → M.val.obj (op W))
      (l : Fin m → N.val.obj (op W)),
      (∀ i, TopCat.Presheaf.germ M.val.presheaf W x hxW (s i) = v i) ∧
        ∀ j, TopCat.Presheaf.germ N.val.presheaf W x hxW (l j) = w j := by
  choose Uv hUv sv hsv using fun i : Fin r => TopCat.Presheaf.exists_germ_eq M.val.presheaf (v i)
  choose Uw hUw sw hsw using fun j : Fin m => TopCat.Presheaf.exists_germ_eq N.val.presheaf (w j)
  obtain ⟨W, hxW, hle⟩ := Stacks.SheafOfModules.exists_nbhd_le x
    (Sum.elim Uv Uw) (by rintro (i | j) <;> [exact hUv i; exact hUw j])
  refine ⟨W, hxW, fun i => M.val.presheaf.map (homOfLE (hle (Sum.inl i))).op (sv i),
    fun j => N.val.presheaf.map (homOfLE (hle (Sum.inr j))).op (sw j), fun i => ?_, fun j => ?_⟩
  · exact (TopCat.Presheaf.germ_res_apply M.val.presheaf (homOfLE (hle (Sum.inl i))) x hxW
      (sv i)).trans (hsv i)
  · exact (TopCat.Presheaf.germ_res_apply N.val.presheaf (homOfLE (hle (Sum.inr j))) x hxW
      (sw j)).trans (hsw j)

/-! ### Stalks of a finite locally free sheaf of modules, and of its top exterior power -/

section Bases

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- An ordered basis of the stalk of a sheaf of modules which is finite locally free of
constant rank. -/
noncomputable def stalkBasis
    (F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) (r : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (x : ↥X) :
    Module.Basis (Fin r) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
  Module.Basis.ofRepr (nonempty_stalkLinearEquiv_finsupp F r x).some

/-- **The stalk of the top exterior power of a sheaf of modules with free stalk is free of rank
one**, on the wedge of an ordered basis of the stalk. -/
noncomputable def stalkExteriorPowerTopBasis
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E) (n : ℕ) (x : ↥X)
    (b : Module.Basis (Fin n) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E.val.presheaf x)) :
    Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk (A.exteriorPower n).val.presheaf x) :=
  (Stacks.ExteriorPower.topBasis b).map
    (_root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior A.exteriorGenerator
      A.exterior_isExteriorAlgebra n x).symm

/-- **The stalk of the source of the comparison is free of rank one.** It is the tensor product
of the stalks of the two top exterior powers, each of which is free of rank one. -/
noncomputable def stalkTensorTopBasis
    (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E')
    (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E'') (r' m : ℕ) (x : ↥X)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' m] :
    Module.Basis (Fin 1) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk
          (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower r')
            (A''.exteriorPower m)).presheaf x) :=
  ((Module.Basis.tensorProduct (Stacks.ExteriorPower.topBasis (stalkBasis E' r' x))
      (Stacks.ExteriorPower.topBasis (stalkBasis E'' m x))).reindex
    Stacks.ExteriorPower.finOneProdEquiv).map
      (((PresheafOfModules.tensorSheafStalkEquiv Osharp (A'.exteriorPower r')
          (A''.exteriorPower m) x).trans
        (TensorProduct.congr
          (_root_.SheafOfModules.exteriorPowerStalkEquiv A'.exterior A'.exteriorGenerator
            A'.exterior_isExteriorAlgebra r' x)
          (_root_.SheafOfModules.exteriorPowerStalkEquiv A''.exterior A''.exteriorGenerator
            A''.exterior_isExteriorAlgebra m x))).symm)

/-- **The comparison of Tag 01CH together with its value on a germ of a wedge of sections**,
bundled so that the stalk of the degree-`n` exterior power can be identified with the degree-`n`
exterior power of the stalk without naming the comparison again. -/
theorem exists_exteriorPowerStalkEquiv_wedgeSec
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E) (n : ℕ) (x : ↥X) :
    ∃ e : ↑(TopCat.Presheaf.stalk (A.exteriorPower n).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^n ↑(TopCat.Presheaf.stalk E.val.presheaf x),
      ∀ (W : Opens ↥X) (hxW : x ∈ W) (t : Fin n → E.val.obj (op W)),
        e (TopCat.Presheaf.germ (A.exteriorPower n).val.presheaf W x hxW
            (wedgeSec A (op W) n t)) =
          exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) n
            fun i => TopCat.Presheaf.germ E.val.presheaf W x hxW (t i) :=
  ⟨_root_.SheafOfModules.exteriorPowerStalkEquiv A.exterior A.exteriorGenerator
      A.exterior_isExteriorAlgebra n x,
    fun W hxW t => _root_.SheafOfModules.exteriorPowerStalkEquiv_germ_homogeneousProd
      A.exterior A.exteriorGenerator A.exterior_isExteriorAlgebra n x W hxW t⟩

end Bases

/-! ### The stalk sequence -/

section StalkExact

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **The stalk of a short exact sequence of sheaves of modules is short exact**, in the
spelling of `PresheafOfModules.stalkMapL`: the first map is injective, the second is surjective,
and the range of the first is the kernel of the second. -/
theorem stalkMapL_shortExact (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g] (x : ↥X) :
    Function.Injective (PresheafOfModules.stalkMapL x f.val) ∧
      Function.Surjective (PresheafOfModules.stalkMapL x g.val) ∧
        LinearMap.range (PresheafOfModules.stalkMapL x f.val) =
          LinearMap.ker (PresheafOfModules.stalkMapL x g.val) := by
  have hstalk := (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact
    (ShortComplex.mk f g hfg)).1 (ShortComplex.ShortExact.mk' hS inferInstance inferInstance) x
  have hzero : ∀ z, PresheafOfModules.stalkMapL x g.val
      (PresheafOfModules.stalkMapL x f.val z) = 0 := by
    intro z
    obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq E'.val.presheaf z
    have hcomp : g.val.app (op U) (f.val.app (op U) s) = 0 :=
      ((_root_.SheafOfModules.comp_val_app_apply f g (op U) s).symm.trans
        (congrArg (fun φ : E' ⟶ E'' => φ.val.app (op U) s) hfg)).trans rfl
    refine Eq.trans (congrArg (PresheafOfModules.stalkMapL x g.val)
      (PresheafOfModules.stalkMapL_germ x f.val U hxU s)) ?_
    refine Eq.trans (PresheafOfModules.stalkMapL_germ x g.val U hxU
      (f.val.app (op U) s)) ?_
    exact Eq.trans (congrArg
      (fun y => TopCat.Presheaf.germ E''.val.presheaf U x hxU y) hcomp) (map_zero _)
  refine ⟨fun a b hab => ?_, fun c => ?_, le_antisymm ?_ ?_⟩
  · exact (ModuleCat.mono_iff_injective _).1 hstalk.mono_f hab
  · exact (ModuleCat.epi_iff_surjective _).1 hstalk.epi_g c
  · rintro _ ⟨a, rfl⟩
    exact hzero a
  · intro y hy
    have hy0 : PresheafOfModules.stalkMapL x g.val y = 0 := LinearMap.mem_ker.1 hy
    exact (ShortComplex.moduleCat_exact_iff _).1 hstalk.exact y hy0

/-- **An ordered basis of the middle stalk of a short exact sequence of sheaves of modules whose
two ends are finite locally free of constant rank.** Its first `r'` members are the images of
`Stacks.SheafOfModules.TopWedge.stalkBasis` of `E'`, and the wedge of the whole family generates
the top exterior power of the middle stalk.

The exactness of the stalk sequence is taken as a hypothesis; it is supplied by
`Stacks.SheafOfModules.TopWedge.stalkMapL_shortExact`. -/
theorem exists_basis_append_stalk (f : E' ⟶ E) (g : E ⟶ E'') (r' k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' (k + 1)]
    (x : ↥X) (hinj : Function.Injective (PresheafOfModules.stalkMapL x f.val))
    (hsurj : Function.Surjective (PresheafOfModules.stalkMapL x g.val))
    (hex : LinearMap.range (PresheafOfModules.stalkMapL x f.val) =
      LinearMap.ker (PresheafOfModules.stalkMapL x g.val)) :
    ∃ (w : Fin (k + 1) → ↑(TopCat.Presheaf.stalk E.val.presheaf x))
      (_ : Module.Basis (Fin (r' + (k + 1))) ↑(TopCat.Presheaf.stalk Osharp.obj x)
        ↑(TopCat.Presheaf.stalk E.val.presheaf x)),
      Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
        {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + (k + 1))
          (Fin.append
            (fun i => PresheafOfModules.stalkMapL x f.val (stalkBasis E' r' x i)) w)} = ⊤ := by
  obtain ⟨w, bM, _, hspan⟩ := Stacks.ExteriorPower.exists_span_ιMulti_append_eq_top
    (PresheafOfModules.stalkMapL x f.val) (PresheafOfModules.stalkMapL x g.val)
    hinj hsurj hex (stalkBasis E' r' x) (stalkBasis E'' (k + 1) x)
  exact ⟨w, bM, hspan⟩

end StalkExact

/-! ### Surjectivity on stalks -/

section Surjective

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **The wedge-and-lift formula puts the wedge of the appended family in the image of the stalk
map.** The finitely many germs involved — a basis of `E'_x` and the given family `w` in `E_x` —
are realised by sections over one neighbourhood of `x`, and the germ of the image of the
corresponding pure tensor is computed by
`Stacks.SheafOfModules.TopWedge.detComparison_wedge`. -/
theorem exists_apply_eq_ιMulti_append
    (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E')
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E)
    (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E'')
    (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g] (r' k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r'] (x : ↥X)
    (w : Fin (k + 1) → ↑(TopCat.Presheaf.stalk E.val.presheaf x))
    (e : ↑(TopCat.Presheaf.stalk (A.exteriorPower (r' + (k + 1))).val.presheaf x)
        ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      ⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(r' + (k + 1))
        ↑(TopCat.Presheaf.stalk E.val.presheaf x))
    (he : ∀ (W : Opens ↥X) (hxW : x ∈ W) (t : Fin (r' + (k + 1)) → E.val.obj (op W)),
      e (TopCat.Presheaf.germ (A.exteriorPower (r' + (k + 1))).val.presheaf W x hxW
          (wedgeSec A (op W) (r' + (k + 1)) t)) =
        exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + (k + 1))
          fun i => TopCat.Presheaf.germ E.val.presheaf W x hxW (t i)) :
    ∃ ξ, e (PresheafOfModules.stalkMapL x
        (detComparison A' A A'' f g hfg hS r' k).val ξ) =
      exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + (k + 1))
        (Fin.append
          (fun i => PresheafOfModules.stalkMapL x f.val (stalkBasis E' r' x i)) w) := by
  obtain ⟨W, hxW, s, l, hs, hl⟩ := exists_common_germ E' E x
    (fun i => stalkBasis E' r' x i) w
  refine ⟨TopCat.Presheaf.germ
    (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj (A'.exteriorPower r')).obj
        (A''.exteriorPower (k + 1))).val.presheaf W x hxW
    ((PresheafOfModules.tensorSheafUnit (A'.exteriorPower r')
        (A''.exteriorPower (k + 1))).app (op W)
      (wedgeSec A' (op W) r' s ⊗ₜ
        wedgeSec A'' (op W) (k + 1) fun j => g.val.app (op W) (l j))), ?_⟩
  refine Eq.trans (congrArg (fun y => e y)
    ((PresheafOfModules.stalkMapL_germ x (detComparison A' A A'' f g hfg hS r' k).val W hxW
      ((PresheafOfModules.tensorSheafUnit (A'.exteriorPower r')
          (A''.exteriorPower (k + 1))).app (op W)
        (wedgeSec A' (op W) r' s ⊗ₜ
          wedgeSec A'' (op W) (k + 1) fun j => g.val.app (op W) (l j)))).trans
      (congrArg
        (fun y => TopCat.Presheaf.germ (A.exteriorPower (r' + (k + 1))).val.presheaf W x hxW y)
        (detComparison_wedge A' A A'' f g hfg hS r' k (op W) s l)))) ?_
  refine Eq.trans (he W hxW (Fin.append (fun i => f.val.app (op W) (s i)) l)) ?_
  refine congrArg (fun t => exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x)
    (r' + (k + 1)) t) ?_
  refine Eq.trans (fin_append_comp
    (fun y => TopCat.Presheaf.germ E.val.presheaf W x hxW y)
    (fun i => f.val.app (op W) (s i)) l) ?_
  refine congrArg₂ Fin.append (funext fun i => ?_) (funext fun j => hl j)
  exact (PresheafOfModules.stalkMapL_germ x f.val W hxW (s i)).symm.trans
    (congrArg (PresheafOfModules.stalkMapL x f.val) (hs i))

/-- **The comparison is surjective on the stalk at `x`** as soon as the wedge of the family
produced by the wedge-and-lift formula generates the top exterior power of `E_x`: that wedge is
in the image, and it generates. -/
theorem surjective_stalkMapL_detComparison
    (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E')
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E)
    (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E'')
    (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g] (r' k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r'] (x : ↥X)
    (w : Fin (k + 1) → ↑(TopCat.Presheaf.stalk E.val.presheaf x))
    (hspan : Submodule.span ↑(TopCat.Presheaf.stalk Osharp.obj x)
      {exteriorPower.ιMulti ↑(TopCat.Presheaf.stalk Osharp.obj x) (r' + (k + 1))
        (Fin.append
          (fun i => PresheafOfModules.stalkMapL x f.val (stalkBasis E' r' x i)) w)} = ⊤) :
    Function.Surjective (PresheafOfModules.stalkMapL x
      (detComparison A' A A'' f g hfg hS r' k).val) := by
  obtain ⟨e, he⟩ := exists_exteriorPowerStalkEquiv_wedgeSec A (r' + (k + 1)) x
  obtain ⟨ξ, hξ⟩ := exists_apply_eq_ιMulti_append A' A A'' f g hfg hS r' k x w e he
  exact Stacks.ExteriorPower.surjective_of_span_singleton_eq_top
    (L := ↑(TopCat.Presheaf.stalk
      (PresheafOfModules.tensorSheafVal Osharp (A'.exteriorPower r')
        (A''.exteriorPower (k + 1))).presheaf x)) _ e hspan ξ hξ

/-- **The comparison is bijective on every stalk.** Surjectivity is the content; injectivity
follows because both stalks are free of rank one over the stalk ring. -/
theorem bijective_stalkMapL_detComparison
    (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E')
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E)
    (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E'')
    (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g] (r' k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' (k + 1)]
    (x : ↥X) :
    Function.Bijective (PresheafOfModules.stalkMapL x
      (detComparison A' A A'' f g hfg hS r' k).val) := by
  obtain ⟨hinj, hsurj, hex⟩ := stalkMapL_shortExact f g hfg hS x
  obtain ⟨w, bM, hspan⟩ := exists_basis_append_stalk f g r' k x hinj hsurj hex
  have hsurjψ := surjective_stalkMapL_detComparison A' A A'' f g hfg hS r' k x w hspan
  refine ⟨?_, hsurjψ⟩
  exact Stacks.ExteriorPower.injective_of_surjective_of_basis_fin_one
    (stalkTensorTopBasis A' A'' r' (k + 1) x)
    (stalkExteriorPowerTopBasis A (r' + (k + 1)) x bM) _ hsurjψ

end Surjective

/-! ### The isomorphism clause -/

section Iso

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **Stacks 0B38, the isomorphism clause in the constant-rank form.** For a short exact
sequence `0 → E' → E → E'' → 0` of sheaves of modules on a ringed space with `E'` finite
locally free of constant rank `r'` and `E''` finite locally free of constant rank `k + 1`, the
canonical comparison `⋀^{r'} E' ⊗ ⋀^{k+1} E'' ⟶ ⋀^{r'+k+1} E` is an isomorphism.

The canonical map `det(E') ⊗ det(E'') ⟶ det(E)` shown invertible here is
`Stacks.SheafOfModules.TopWedge.detComparison`. Here `det` is the top exterior power, identified
with the `det` of [Stacks, Tag 0FJN] at constant rank by
`SheafOfModules.TensorExteriorSymmetricAlgebras.determinantIsoExteriorPower`; what is carried
here is `E'` of constant rank `r'` and `E''` of constant rank `r'' = k + 1`.

This is the CONSTANT-RANK form of the tag. The general case — a short exact sequence of finite
locally free sheaves with no constant-rank hypothesis — is carried by
`Stacks.SheafOfModules.TopWedge.isIso_determinantTensorDeterminantHom` and
`Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantIsoOfFiniteLocallyFree` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExactIso`. -/
@[stacks 0B38 "the ISOMORPHISM clause, in the constant-rank form",
  sga "6 X 5.1" "special case",
  sga "6 X 6.2.7" "(6.2.9), special case"]
theorem isIso_detComparison
    (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E')
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E)
    (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology ↥X) E'')
    (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g] (r' k : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' r']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E'' (k + 1)] :
    IsIso (detComparison A' A A'' f g hfg hS r' k) := by
  refine (AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap
    (O := toRingCat (Opens.grothendieckTopology ↥X) Osharp)
    (detComparison A' A A'' f g hfg hS r' k)).2 fun x => ?_
  obtain ⟨hinj, hsurj⟩ := bijective_stalkMapL_detComparison A' A A'' f g hfg hS r' k x
  refine ⟨fun a b hab => ?_, fun ζ => ?_⟩
  · exact hinj hab
  · exact hsurj ζ

end Iso

end Stacks.SheafOfModules.TopWedge

end
