module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleFactorThru
import StacksCore.Tactic.StacksAttribute

/-!
# The canonical map `det(E') ⊗ det(E'') ⟶ det(E)` of a short exact sequence

Let `(X, O_X)` be a ringed space and let `0 → E' → E → E'' → 0` be a short exact sequence of
sheaves of `O_X`-modules with `E'` and `E''` **finite locally free of no particular rank**.
[Stacks, Tag 0B38] asserts a canonical isomorphism `det(E') ⊗ det(E'') ⟶ det(E)` of the
determinants of [Stacks, Tag 0FJN]. This file constructs the canonical **map**, in three steps.

`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExact` builds, with no rank
hypothesis, the comparison `det(E')ₙ ⊗ ⋀ᵏ⁺¹ E'' ⟶ ⋀ⁿ⁺ᵏ⁺¹ E` out of the degree-`n` summand
`det(E')ₙ` of the determinant. Here

1. the second factor is cut down to the degree-`m` summand of `det(E'')`, where for `m = 0` the
   presentation of [Stacks, Tag 01CJ] is replaced by the degree-zero identification of the two
   exterior algebras, there being nothing to descend along;
2. the image is shown to lie in the degree-`n+m` summand of `det(E)`, giving
   `det(E')ₙ ⊗ det(E'')ₘ ⟶ det(E)ₙ₊ₘ` for every pair of degrees;
3. the family is assembled over the degrees into `det(E') ⊗ det(E'') ⟶ det(E)`, using that the
   tensor product of sheaves of modules preserves coproducts in each variable
   (`Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafRight` and
   `...tensorSheafLeft`) and that `det` is the coproduct of its summands over the degrees.

**That the assembled map is an isomorphism** is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExactIso`, which completes
[Stacks, Tag 0B38] in the general case; the map itself carries the tag here.

## Main definitions

* `Stacks.SheafOfModules.TopWedge.annTensorExteriorHom` and
  `Stacks.SheafOfModules.TopWedge.annTensorExteriorHomZero`: the comparison with its second
  factor cut down, `det(E')ₙ ⊗ det(E'')ₘ ⟶ ⋀ⁿ⁺ᵐ E`, for `m = k + 1` and for `m = 0`.
* `Stacks.SheafOfModules.TopWedge.annTensorAnnHom`,
  `Stacks.SheafOfModules.TopWedge.annTensorAnnHomZero` and
  `Stacks.SheafOfModules.TopWedge.detSummandComparison`: **the comparison between summands**
  `det(E')ₙ ⊗ det(E'')ₘ ⟶ det(E)ₙ₊ₘ`, in the two shapes and then in every pair of degrees.
* `Stacks.SheafOfModules.TopWedge.detTensorAnnComparison`: the comparison
  `det(E') ⊗ det(E'')ₘ ⟶ det(E)`, assembled over the degrees of the first factor.
* `Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantHom`: **the canonical map
  `det(E') ⊗ det(E'') ⟶ det(E)` of [Stacks, Tag 0B38]**, with no rank hypothesis. It is an
  isomorphism, by
  `Stacks.SheafOfModules.TopWedge.isIso_determinantTensorDeterminantHom`.
* `Stacks.SheafOfModules.TopWedge.exteriorPowerZeroIso`: the identification of the degree-zero
  exterior powers of two sheaves of modules, both being the structure sheaf.

## Main results

* `Stacks.SheafOfModules.TopWedge.isExteriorAnnihilated_of_subsingleton_dichotomy`: a general
  criterion — **a morphism into `⋀ᵈ E` takes exterior annihilated values as soon as at every
  point either the stalk of its source vanishes or `⋀ᵈ⁺¹` of the stalk of `E` does.** This is
  what makes the comparison land in the determinant without any rank hypothesis.
* `Stacks.SheafOfModules.TopWedge.subsingleton_or_subsingleton_exteriorPower_stalk`: **the
  dichotomy holds for the source of the comparison**, at every point of the space.
* `Stacks.SheafOfModules.TopWedge.subsingleton_stalk_exteriorAnnihilator_of_stalkLinearEquiv`:
  the stalk of `det(F)ₙ` vanishes at a point where the stalk of `F` is free of rank `r ≠ n`.
* `Stacks.SheafOfModules.TopWedge.nonempty_stalkBasis_append`: the stalk of `E` is free of rank
  `rank_x E' + rank_x E''`.
* `Stacks.SheafOfModules.TopWedge.annTensorAnnHom_ι` and
  `Stacks.SheafOfModules.TopWedge.annTensorAnnHomZero_ι`: the comparison between summands,
  composed with the inclusion of `det(E)ₙ₊ₘ` into `⋀ⁿ⁺ᵐ E`, is the comparison into the exterior
  power.
* `Stacks.SheafOfModules.TopWedge.map_determinantSummand_comp_determinantTensorDeterminantHom`
  and `Stacks.SheafOfModules.TopWedge.map_determinantSummand_comp_detTensorAnnComparison`: the
  two defining equations of the assembled map, which determine it because the summand inclusions
  are jointly epimorphic.

## Implementation notes

**The dichotomy.** The point of the second step is that the two reasons for which a product
`a ∧ ψ(ξ)` of a degree-one section with a value of the comparison can vanish exhaust all points
of the space, with no constant-rank hypothesis anywhere. At a point `x` write `r'` and `r''` for
the ranks of `E'` and of `E''` there, which exist because both are finite locally free but need
not be locally constant. If `n ≠ r'` or `m ≠ r''` then one of the two factors of the source has
vanishing stalk at `x` — the degreewise annihilator of a finite free module is concentrated in
its rank — and a tensor product with a vanishing factor vanishes, so the germ of `ξ` is already
zero. In the remaining case `n + m = r' + r''`, which is the rank of `E` at `x` because the stalk
sequence is short exact with free ends, so `⋀ⁿ⁺ᵐ⁺¹` of the stalk of `E` vanishes and the germ of
the product is zero for that reason. Vanishing of a section of a sheaf is local, so that is
enough.

**How the isomorphism clause is proved.** Isomorphy is stalkwise
(`AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap`), and at a point `x` with
`r' = rank_x E'` and `r'' = rank_x E''` every summand of source and target except `(r', r'')`
and `r' + r''` has vanishing stalk there, by
`Stacks.SheafOfModules.TopWedge.subsingleton_stalk_exteriorAnnihilator_of_stalkLinearEquiv`. The
surviving stalks are then free of rank one and the comparison between the surviving summands is
surjective there by the wedge-and-lift formula, which gives surjectivity; injectivity is free by
the Orzech property (`Stacks.ExteriorPower.injective_of_surjective_of_basis_fin_one`). This is
carried out in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExactIso`;
see its implementation notes.

**Why the stalk bases are passed as data.** The repository's stalk-basis lemmas for a short
exact sequence (`Stacks.SheafOfModules.TopWedge.exists_basis_append_stalk` and the lemmas
around it) take the ranks from global `IsFiniteLocallyFreeOfRank` instances. Here the rank
varies from point to point, so the bases are produced at each point by
`Stacks.SheafOfModules.TopWedge.exists_nonempty_stalkLinearEquiv_finsupp` and passed to the
linear-algebra lemmas directly; nothing in those lemmas used more than the bases.

**Cutting the proofs up.** As in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExactIso`, every mention of
`PresheafOfModules.stalkMapL` or of a stalk comparison makes the elaborator re-solve the module
structure on a stalk and unify a functor composition against `CategoryTheory.Sheaf.toRingCat`,
and two such steps in one declaration exhaust the heartbeat budget although either alone is
comfortable. The facts are therefore passed between declarations as explicit hypotheses.

**Two spellings of the sheaf of rings.** `CategoryTheory.Sheaf.toRingCat Osharp` and
`Stacks.SheafOfModules.Tensor.ringSheaf Osharp` are reducibly equal but not
syntactically so: the first is the sheaf given by the explicit presheaf `Osharp.obj ⋙ forget₂ _ _`
and the second is `sheafCompose` applied to `Osharp`. The determinant and its summands are
written over the first, while the tensor-product functors of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorProductRightExact` are stated over the
second, so applying one of those functors to a summand produces a family of sheaves of modules
whose stated ring sheaf is the second spelling. Instance search matches syntactically, so the
coproduct and colimit-preservation instances this file needs are supplied in both spellings;
without that the coproduct of the determinant summands is not found in the position where the
tensor functor consumes it.

## References

* [Stacks Project, Tag 0B38](https://stacks.math.columbia.edu/tag/0B38)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf
open scoped TensorProduct

universe u

/-! ### A tensor product with a vanishing factor vanishes -/

namespace Stacks.ExteriorPower

/-- **A tensor product one of whose factors vanishes vanishes.** Every element is a sum of pure
tensors, and a pure tensor with a zero factor is zero. -/
theorem subsingleton_tensorProduct_left {R : Type u} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Subsingleton M] :
    Subsingleton (M ⊗[R] N) :=
  inferInstance

/-- **A tensor product one of whose factors vanishes vanishes**, in the second variable. -/
theorem subsingleton_tensorProduct_right {R : Type u} [CommRing R] {M N : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Subsingleton N] :
    Subsingleton (M ⊗[R] N) :=
  inferInstance

end Stacks.ExteriorPower

namespace Stacks.SheafOfModules.TopWedge

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-! ### Vanishing stalks of a tensor product of sheaves of modules -/

section TensorStalk

variable (F G : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (x : ↥X)

/-- **The stalk of a tensor product of sheaves of modules vanishes as soon as the stalk of the
first factor does.** The stalk of the tensor product is the tensor product of the stalks
([Stacks, Tag 01CB]). -/
theorem subsingleton_stalk_tensorSheaf_of_left
    (h : Subsingleton (ToType (TopCat.Presheaf.stalk F.val.presheaf x))) :
    Subsingleton (ToType (TopCat.Presheaf.stalk
      (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G).val.presheaf x)) :=
  have := h
  have : Subsingleton (↑(TopCat.Presheaf.stalk F.val.presheaf x)
      ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)] ↑(TopCat.Presheaf.stalk G.val.presheaf x)) :=
    Stacks.ExteriorPower.subsingleton_tensorProduct_left
  (PresheafOfModules.tensorSheafStalkEquiv Osharp F G x).toEquiv.subsingleton

/-- **The stalk of a tensor product of sheaves of modules vanishes as soon as the stalk of the
second factor does.** -/
theorem subsingleton_stalk_tensorSheaf_of_right
    (h : Subsingleton (ToType (TopCat.Presheaf.stalk G.val.presheaf x))) :
    Subsingleton (ToType (TopCat.Presheaf.stalk
      (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj F).obj G).val.presheaf x)) :=
  have := h
  have : Subsingleton (↑(TopCat.Presheaf.stalk F.val.presheaf x)
      ⊗[↑(TopCat.Presheaf.stalk Osharp.obj x)] ↑(TopCat.Presheaf.stalk G.val.presheaf x)) :=
    Stacks.ExteriorPower.subsingleton_tensorProduct_right
  (PresheafOfModules.tensorSheafStalkEquiv Osharp F G x).toEquiv.subsingleton

end TensorStalk

/-! ### Vanishing stalks of a determinant summand -/

section AnnihilatorStalk

variable {E' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')

/-- **The stalk of the degree-`n` summand of the determinant vanishes at a point where the stalk
of `E'` is free of rank `r ≠ n`.** This is
`SheafOfModules.TensorExteriorSymmetricAlgebras.subsingleton_stalk_exteriorAnnihilator` with the
freeness of the stalk given as data instead of deduced from a globally constant rank. -/
theorem subsingleton_stalk_exteriorAnnihilator_of_stalkLinearEquiv (x : ↥X) (r : ℕ)
    (e : ↑(TopCat.Presheaf.stalk E'.val.presheaf x)
      ≃ₗ[↑(TopCat.Presheaf.stalk Osharp.obj x)]
      (Fin r →₀ ↑(TopCat.Presheaf.stalk Osharp.obj x))) (n : ℕ) (hn : n ≠ r) :
    Subsingleton (ToType (TopCat.Presheaf.stalk
      (A'.exteriorAnnihilator n).toSheafOfModules.val.presheaf x)) := by
  refine subsingleton_of_forall_eq 0 fun a => ?_
  refine _root_.SheafOfModules.TensorExteriorSymmetricAlgebras.injective_submoduleStalkι x ?_
  rw [map_zero]
  obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (A'.exteriorAnnihilator n).toSheafOfModules.val.presheaf a
  rw [_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.submoduleStalkι_germ x U hx s]
  exact germ_eq_zero_of_isExteriorAnnihilated A' x r e n hn hx _ (Subtype.property s)

end AnnihilatorStalk

/-! ### The rank of the middle term at a point -/

section MiddleBasis

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- **An ordered basis of the middle stalk of a short exact sequence of sheaves of modules whose
two ends have free stalks**, of the sum of the two ranks. The exactness of the stalk sequence is
taken as a hypothesis; it is supplied by
`Stacks.SheafOfModules.TopWedge.stalkMapL_shortExact`. -/
theorem nonempty_stalkBasis_append (f : E' ⟶ E) (g : E ⟶ E'') (x : ↥X)
    (hinj : Function.Injective (PresheafOfModules.stalkMapL x f.val))
    (hsurj : Function.Surjective (PresheafOfModules.stalkMapL x g.val))
    (hex : LinearMap.range (PresheafOfModules.stalkMapL x f.val) =
      LinearMap.ker (PresheafOfModules.stalkMapL x g.val))
    {r' r'' : ℕ}
    (b' : Module.Basis (Fin r') ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E'.val.presheaf x))
    (b'' : Module.Basis (Fin r'') ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E''.val.presheaf x)) :
    Nonempty (Module.Basis (Fin (r' + r'')) ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk E.val.presheaf x)) := by
  obtain ⟨w, bM, _⟩ := Stacks.ExteriorPower.exists_basis_append
    (PresheafOfModules.stalkMapL x f.val) (PresheafOfModules.stalkMapL x g.val)
    hinj hsurj hex b' b''
  exact ⟨bM⟩

end MiddleBasis

/-! ### A criterion for a morphism to land in the determinant -/

section Dichotomy

variable {E : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  {S : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- A value of a morphism out of `S` has vanishing germ at a point where the stalk of `S`
vanishes. -/
theorem germ_apply_eq_zero_of_subsingleton_stalk {d : ℕ} (ψ : S ⟶ A.exteriorPower d) (x : ↥X)
    (hsub : Subsingleton (ToType (TopCat.Presheaf.stalk S.val.presheaf x)))
    {V : Opens ↥X} (hx : x ∈ V) (ξ : ToType (S.val.obj (op V))) :
    Stacks.SheafOfModules.germ (A.exteriorPower d) x hx (ψ.val.app (op V) ξ) = 0 := by
  have h0 : Stacks.SheafOfModules.germ S x hx ξ = 0 := Subsingleton.elim _ _
  exact Eq.trans (PresheafOfModules.stalkMapL_germ x ψ.val V hx ξ).symm
    (Eq.trans (congrArg (PresheafOfModules.stalkMapL x ψ.val) h0) (map_zero _))

/-- **The product of a degree-one section with a section of `⋀ᵈ E` whose germ vanishes has
vanishing germ.** -/
theorem germ_wedgeGen_eq_zero_of_germ_eq_zero {d : ℕ} (x : ↥X) {V : Opens ↥X} (hx : x ∈ V)
    (t : ToType ((A.exteriorPower d).val.obj (op V)))
    (ht : Stacks.SheafOfModules.germ (A.exteriorPower d) x hx t = 0)
    (a : ToType (E.val.obj (op V))) :
    Stacks.SheafOfModules.germ (A.exteriorPower (d + 1)) x hx (A.wedgeGen d (op V) a t) = 0 := by
  obtain ⟨W, fW, hxW, hres⟩ := Stacks.SheafOfModules.exists_res_eq x hx t 0
    (ht.trans (Stacks.SheafOfModules.germ_zero x hx).symm)
  have ht0 : Stacks.SheafOfModules.res (A.exteriorPower d) fW t = 0 :=
    hres.trans (Stacks.SheafOfModules.res_zero (A.exteriorPower d) fW)
  have hzero : Stacks.SheafOfModules.res (A.exteriorPower (d + 1)) fW
      (A.wedgeGen d (op V) a t) = 0 := by
    rw [_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.wedgeGen_res d fW a t, ht0,
      _root_.SheafOfModules.TensorExteriorSymmetricAlgebras.wedgeGen_zero_right]
  refine Eq.trans (Stacks.SheafOfModules.germ_res x fW hxW _).symm ?_
  exact Eq.trans (congrArg (Stacks.SheafOfModules.germ (A.exteriorPower (d + 1)) x hxW) hzero)
    (Stacks.SheafOfModules.germ_zero x hxW)

/-- **Every germ of the product of a degree-one section with a value of `ψ` vanishes**, under the
dichotomy: at each point either the stalk of the source of `ψ` vanishes, so the value already
has vanishing germ, or `⋀ᵈ⁺¹` of the stalk of `E` vanishes, so every germ in that degree does. -/
theorem germ_wedgeGen_apply_eq_zero_of_dichotomy {d : ℕ} (ψ : S ⟶ A.exteriorPower d)
    (hdich : ∀ y : ↥X, Subsingleton (ToType (TopCat.Presheaf.stalk S.val.presheaf y)) ∨
      Subsingleton (⋀[↑(TopCat.Presheaf.stalk Osharp.obj y)]^(d + 1)
        ↑(TopCat.Presheaf.stalk E.val.presheaf y)))
    (x : ↥X) {V : Opens ↥X} (hx : x ∈ V) (ξ : ToType (S.val.obj (op V)))
    (a : ToType (E.val.obj (op V))) :
    Stacks.SheafOfModules.germ (A.exteriorPower (d + 1)) x hx
      (A.wedgeGen d (op V) a (ψ.val.app (op V) ξ)) = 0 := by
  rcases hdich x with hS | hE
  · exact germ_wedgeGen_eq_zero_of_germ_eq_zero A x hx _
      (germ_apply_eq_zero_of_subsingleton_stalk A ψ x hS hx ξ) a
  · exact germ_eq_zero_of_subsingleton_exteriorPower A x (d + 1) hE hx _

/-- **The product of a degree-one section with a value of `ψ` vanishes**, under the dichotomy.
Vanishing of a section of a sheaf is local, so it is enough that every germ vanish. -/
theorem wedgeGen_apply_eq_zero_of_dichotomy {d : ℕ} (ψ : S ⟶ A.exteriorPower d)
    (hdich : ∀ y : ↥X, Subsingleton (ToType (TopCat.Presheaf.stalk S.val.presheaf y)) ∨
      Subsingleton (⋀[↑(TopCat.Presheaf.stalk Osharp.obj y)]^(d + 1)
        ↑(TopCat.Presheaf.stalk E.val.presheaf y)))
    (V : Opens ↥X) (ξ : ToType (S.val.obj (op V))) (a : ToType (E.val.obj (op V))) :
    A.wedgeGen d (op V) a (ψ.val.app (op V) ξ) = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext
    (F := (A.exteriorPower (d + 1)).val.presheaf) (A.exteriorPower (d + 1)).isSheaf ?_
  intro x hx
  obtain ⟨W, fW, hxW, hres⟩ := Stacks.SheafOfModules.exists_res_eq x hx _ 0
    ((germ_wedgeGen_apply_eq_zero_of_dichotomy A ψ hdich x hx ξ a).trans
      (Stacks.SheafOfModules.germ_zero x hx).symm)
  exact ⟨W, fW.le, hxW, hres⟩

/-- **A morphism into `⋀ᵈ E` takes exterior annihilated values** as soon as at every point either
the stalk of its source vanishes or `⋀ᵈ⁺¹` of the stalk of `E` does. This is the criterion by
which the determinant comparison lands in the determinant of the middle term with no rank
hypothesis: see
`Stacks.SheafOfModules.TopWedge.subsingleton_or_subsingleton_exteriorPower_stalk`. -/
theorem isExteriorAnnihilated_of_subsingleton_dichotomy {d : ℕ} (ψ : S ⟶ A.exteriorPower d)
    (hdich : ∀ y : ↥X, Subsingleton (ToType (TopCat.Presheaf.stalk S.val.presheaf y)) ∨
      Subsingleton (⋀[↑(TopCat.Presheaf.stalk Osharp.obj y)]^(d + 1)
        ↑(TopCat.Presheaf.stalk E.val.presheaf y)))
    (V : (Opens ↥X)ᵒᵖ) (ξ : ToType (S.val.obj V)) :
    A.IsExteriorAnnihilated d (ψ.val.app V ξ) := by
  intro W h a
  have hnat : ψ.val.app W (S.val.map h ξ) =
      (A.exteriorPower d).val.map h (ψ.val.app V ξ) :=
    PresheafOfModules.naturality_apply ψ.val h ξ
  refine Eq.trans (congrArg (fun z => (A.exterior.mul 1 (d : ℤ)).app W
    (A.exteriorGenerator.val.app W a) z) hnat.symm) ?_
  exact (_root_.SheafOfModules.TensorExteriorSymmetricAlgebras.wedgeGen_eq_zero_iff d W a _).mp
    (wedgeGen_apply_eq_zero_of_dichotomy A ψ hdich W.unop (S.val.map h ξ) a)

end Dichotomy

/-! ### The comparison between determinant summands -/

section Summand

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E'')
  (f : E' ⟶ E) (g : E ⟶ E'')

/-- **The dichotomy at a point** for the source `det(E')ₙ ⊗ det(E'')ₘ` of the comparison: either
that stalk vanishes, because the degree of one of the two factors is not the rank of the
corresponding sheaf there, or `⋀ⁿ⁺ᵐ⁺¹` of the stalk of `E` vanishes, because the stalk of `E` is
free of rank `n + m` there.

The ranks of `E'` and `E''` at the point are produced by
`Stacks.SheafOfModules.TopWedge.exists_nonempty_stalkLinearEquiv_finsupp` and are not assumed
locally constant. The exactness of the stalk sequence is taken as a hypothesis; it is supplied by
`Stacks.SheafOfModules.TopWedge.stalkMapL_shortExact`. -/
theorem subsingleton_or_subsingleton_exteriorPower_stalk
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (n m : ℕ) (x : ↥X)
    (hinj : Function.Injective (PresheafOfModules.stalkMapL x f.val))
    (hsurj : Function.Surjective (PresheafOfModules.stalkMapL x g.val))
    (hex : LinearMap.range (PresheafOfModules.stalkMapL x f.val) =
      LinearMap.ker (PresheafOfModules.stalkMapL x g.val)) :
    Subsingleton (ToType (TopCat.Presheaf.stalk
        (((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj ((A'.exteriorAnnihilator
            n).toSheafOfModules)).obj ((A''.exteriorAnnihilator m).toSheafOfModules)).val.presheaf
            x)) ∨
      Subsingleton (⋀[↑(TopCat.Presheaf.stalk Osharp.obj x)]^(n + m + 1)
        ↑(TopCat.Presheaf.stalk E.val.presheaf x)) := by
  obtain ⟨r', ⟨e'⟩⟩ := exists_nonempty_stalkLinearEquiv_finsupp E' x
  obtain ⟨r'', ⟨e''⟩⟩ := exists_nonempty_stalkLinearEquiv_finsupp E'' x
  by_cases hn : n = r'
  · by_cases hm : m = r''
    · obtain ⟨bM⟩ := nonempty_stalkBasis_append f g x hinj hsurj hex
        (Module.Basis.ofRepr e') (Module.Basis.ofRepr e'')
      exact Or.inr (Stacks.ExteriorPower.subsingleton_exteriorPower_of_lt bM (by omega))
    · exact Or.inl (subsingleton_stalk_tensorSheaf_of_right _ _ x
        (subsingleton_stalk_exteriorAnnihilator_of_stalkLinearEquiv A'' x r'' e'' m hm))
  · exact Or.inl (subsingleton_stalk_tensorSheaf_of_left _ _ x
      (subsingleton_stalk_exteriorAnnihilator_of_stalkLinearEquiv A' x r' e' n hn))

variable (hfg : f ≫ g = 0)

/-- **The comparison `det(E')ₙ ⊗ det(E'')ₘ ⟶ ⋀ⁿ⁺ᵐ E`** (with `m = k + 1`), obtained from
`Stacks.SheafOfModules.TopWedge.detAnnihilatorComparison` by cutting the second factor down
along the inclusion `det(E'')ₘ ⟶ ⋀ᵐ E''`. No rank hypothesis. -/
noncomputable def annTensorExteriorHom
    (hS : (ShortComplex.mk f g hfg).Exact) [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E'] (n k : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj ((A'.exteriorAnnihilator
        n).toSheafOfModules)).obj ((A''.exteriorAnnihilator (k + 1)).toSheafOfModules) ⟶
      A.exteriorPower (n + (k + 1)) :=
  tensorLeftMapFrom (P := (A'.exteriorAnnihilator n).toSheafOfModules)
      (A''.exteriorAnnihilator (k + 1)).ι ≫
    detAnnihilatorComparison A' A A'' f g hfg hS n k

/-- **The comparison takes exterior annihilated values**, which is the step that makes a map of
determinants out of it. It is the criterion
`Stacks.SheafOfModules.TopWedge.isExteriorAnnihilated_of_subsingleton_dichotomy` applied to the
dichotomy of
`Stacks.SheafOfModules.TopWedge.subsingleton_or_subsingleton_exteriorPower_stalk`. -/
theorem isExteriorAnnihilated_annTensorExteriorHom
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (n k : ℕ)
    (V : (Opens ↥X)ᵒᵖ)
    (ξ : ToType ((((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj ((A'.exteriorAnnihilator
        n).toSheafOfModules)).obj ((A''.exteriorAnnihilator (k + 1)).toSheafOfModules)).val.obj V))
        :
    A.IsExteriorAnnihilated (n + (k + 1))
      ((annTensorExteriorHom A' A A'' f g hfg hS n k).val.app V ξ) :=
  isExteriorAnnihilated_of_subsingleton_dichotomy A
    (annTensorExteriorHom A' A A'' f g hfg hS n k)
    (fun y =>
      have h := stalkMapL_shortExact f g hfg hS y
      subsingleton_or_subsingleton_exteriorPower_stalk A' A'' f g n (k + 1) y h.1 h.2.1 h.2.2)
    V ξ

/-- **The comparison between determinant summands**
`det(E')ₙ ⊗ det(E'')ₘ ⟶ det(E)ₙ₊ₘ` (with `m = k + 1`), for a short exact sequence
`0 → E' → E → E'' → 0` of sheaves of modules with `E'` and `E''` finite locally free of **no
particular rank**.

It is `Stacks.SheafOfModules.TopWedge.annTensorExteriorHom` factored through the inclusion of the
degree-`n+m` summand of `det(E)`, which is possible by
`Stacks.SheafOfModules.TopWedge.isExteriorAnnihilated_annTensorExteriorHom`. -/
noncomputable def annTensorAnnHom
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (n k : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj ((A'.exteriorAnnihilator
        n).toSheafOfModules)).obj ((A''.exteriorAnnihilator (k + 1)).toSheafOfModules) ⟶
      (A.exteriorAnnihilator (n + (k + 1))).toSheafOfModules :=
  (A.exteriorAnnihilator (n + (k + 1))).factorThru
    (annTensorExteriorHom A' A A'' f g hfg hS n k)
    (isExteriorAnnihilated_annTensorExteriorHom A' A A'' f g hfg hS n k)

/-- **The comparison between summands, composed with the inclusion of the summand**, is the
comparison into the exterior power. -/
@[reassoc]
theorem annTensorAnnHom_ι
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (n k : ℕ) :
    annTensorAnnHom A' A A'' f g hfg hS n k ≫ (A.exteriorAnnihilator (n + (k + 1))).ι =
      annTensorExteriorHom A' A A'' f g hfg hS n k :=
  _root_.SheafOfModules.Submodule.factorThru_ι _ _ _

/-! ### The degree-zero case of the second factor -/

/-- **The degree-zero exterior powers of two sheaves of modules are canonically identified**:
both are the structure sheaf, by the degree-zero identification carried by a
`SheafOfModules.TensorExteriorSymmetricAlgebras` structure. This is what replaces the
presentation of [Stacks, Tag 01CJ] in degree zero, where there is nothing to descend along. -/
noncomputable def exteriorPowerZeroIso : A''.exteriorPower 0 ≅ A.exteriorPower 0 :=
  A''.exteriorPieceIso_zero ≪≫ A.exteriorPieceIso_zero.symm

/-- **The comparison `det(E')ₙ ⊗ det(E'')₀ ⟶ ⋀ⁿ E`.** In degree zero of the second factor the
comparison needs no descent: the degree-zero piece of the exterior algebra of `E''` is the
structure sheaf, hence is identified with that of `E`, and the comparison is the wedge map of
`Stacks.SheafOfModules.TopWedge.wedgeHomFrom` in degree zero. Neither exactness nor
finite local freeness is used. -/
noncomputable def annTensorExteriorHomZero (n : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj ((A'.exteriorAnnihilator
        n).toSheafOfModules)).obj ((A''.exteriorAnnihilator 0).toSheafOfModules) ⟶
      A.exteriorPower (n + 0) :=
  tensorLeftMapFrom (P := (A'.exteriorAnnihilator n).toSheafOfModules)
      ((A''.exteriorAnnihilator 0).ι ≫ (exteriorPowerZeroIso A A'').hom) ≫
    wedgeHomFrom A' A f (A'.exteriorAnnihilator n).ι 0

/-- **The degree-zero comparison takes exterior annihilated values.** The dichotomy is the one of
`Stacks.SheafOfModules.TopWedge.subsingleton_or_subsingleton_exteriorPower_stalk` at `m = 0`:
either the stalk of the source vanishes, or `E''` has rank zero at the point and the stalk of `E`
is free of rank `n`. -/
theorem isExteriorAnnihilated_annTensorExteriorHomZero
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (n : ℕ)
    (V : (Opens ↥X)ᵒᵖ)
    (ξ : ToType ((((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj ((A'.exteriorAnnihilator
        n).toSheafOfModules)).obj ((A''.exteriorAnnihilator 0).toSheafOfModules)).val.obj V)) :
    A.IsExteriorAnnihilated (n + 0) ((annTensorExteriorHomZero A' A A'' f n).val.app V ξ) :=
  isExteriorAnnihilated_of_subsingleton_dichotomy A (annTensorExteriorHomZero A' A A'' f n)
    (fun y =>
      have h := stalkMapL_shortExact f g hfg hS y
      subsingleton_or_subsingleton_exteriorPower_stalk A' A'' f g n 0 y h.1 h.2.1 h.2.2)
    V ξ

/-- **The degree-zero comparison between determinant summands**
`det(E')ₙ ⊗ det(E'')₀ ⟶ det(E)ₙ`. -/
noncomputable def annTensorAnnHomZero
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (n : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj ((A'.exteriorAnnihilator
        n).toSheafOfModules)).obj ((A''.exteriorAnnihilator 0).toSheafOfModules) ⟶
      (A.exteriorAnnihilator (n + 0)).toSheafOfModules :=
  (A.exteriorAnnihilator (n + 0)).factorThru (annTensorExteriorHomZero A' A A'' f n)
    (isExteriorAnnihilated_annTensorExteriorHomZero A' A A'' f g hfg hS n)

/-- The degree-zero comparison between summands, composed with the inclusion of the summand, is
the degree-zero comparison into the exterior power. -/
@[reassoc]
theorem annTensorAnnHomZero_ι
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (n : ℕ) :
    annTensorAnnHomZero A' A A'' f g hfg hS n ≫ (A.exteriorAnnihilator (n + 0)).ι =
      annTensorExteriorHomZero A' A A'' f n :=
  _root_.SheafOfModules.Submodule.factorThru_ι _ _ _

/-! ### The comparison in every pair of degrees -/

/-- **The comparison between determinant summands in every pair of degrees**,
`det(E')ₙ ⊗ det(E'')ₘ ⟶ det(E)ₙ₊ₘ`, for a short exact sequence `0 → E' → E → E'' → 0` of
sheaves of modules with `E'` and `E''` finite locally free of **no particular rank**.

For `m = k + 1` this is `Stacks.SheafOfModules.TopWedge.annTensorAnnHom`, the descent of the
wedge map along the presentation of [Stacks, Tag 01CJ]; for `m = 0` it is
`Stacks.SheafOfModules.TopWedge.annTensorAnnHomZero`, where the presentation is replaced by the
degree-zero identification of the two exterior algebras.

This is the family a map `det(E') ⊗ det(E'') ⟶ det(E)` has to be assembled from, `det` being the
coproduct of its summands over the degrees. -/
noncomputable def detSummandComparison
    (hS : (ShortComplex.mk f g hfg).Exact) [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (n m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj ((A'.exteriorAnnihilator
        n).toSheafOfModules)).obj ((A''.exteriorAnnihilator m).toSheafOfModules) ⟶
      (A.exteriorAnnihilator (n + m)).toSheafOfModules :=
  match m with
  | 0 => annTensorAnnHomZero A' A A'' f g hfg hS n
  | k + 1 => annTensorAnnHom A' A A'' f g hfg hS n k

end Summand

/-! ### Assembling the comparison over the degrees -/

section Assembly

variable {E' E E'' : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- Tensoring on the left with a fixed factor preserves colimits of the smallest size, hence
in particular an `ℕ`-indexed coproduct. The generic instance is instantiated by hand, as in
`Stacks.SheafOfModules.TopWedge.preservesColimit_parallelPair_tensorLeftFunctorFrom`: at the
concrete site the search for it no longer succeeds in this import closure. -/
instance preservesSmallestColimits_tensorSheafRight
    (F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :
    Limits.PreservesColimitsOfSize.{0, 0}
      (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
        (Opens.grothendieckTopology ↥X) Osharp F) :=
  have := Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafRight
    (Opens.grothendieckTopology ↥X) Osharp F
  Limits.preservesColimitsOfSize_shrink.{0, u, 0, u} _

/-- Tensoring on the right with a fixed factor preserves colimits of the smallest size. -/
instance preservesSmallestColimits_tensorSheafLeft
    (G : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :
    Limits.PreservesColimitsOfSize.{0, 0}
      (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
        (Opens.grothendieckTopology ↥X) Osharp G) :=
  have := Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafLeft
    (Opens.grothendieckTopology ↥X) Osharp G
  Limits.preservesColimitsOfSize_shrink.{0, u, 0, u} _

/-- Tensoring on the left with a fixed factor preserves colimits of the shape of an `ℕ`-indexed
coproduct. The shape universes of `CategoryTheory.Limits.PreservesColimitsOfSize` are output
parameters, so they are pinned here by naming the shape rather than left to instance search. -/
theorem preservesColimitsOfShape_discrete_tensorSheafRight
    (F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :
    Limits.PreservesColimitsOfShape (Discrete ℕ)
      (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
        (Opens.grothendieckTopology ↥X) Osharp F) :=
  Limits.PreservesColimitsOfSize.preservesColimitsOfShape

/-- Tensoring on the right with a fixed factor preserves colimits of the shape of an `ℕ`-indexed
coproduct. -/
theorem preservesColimitsOfShape_discrete_tensorSheafLeft
    (G : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)) :
    Limits.PreservesColimitsOfShape (Discrete ℕ)
      (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
        (Opens.grothendieckTopology ↥X) Osharp G) :=
  Limits.PreservesColimitsOfSize.preservesColimitsOfShape

/-- Tensoring on the left with a fixed factor preserves an `ℕ`-indexed coproduct. The family is
written over `Stacks.SheafOfModules.Tensor.ringSheaf`, which is the spelling
of the sheaf of rings that applying the functor produces; see the implementation notes. -/
instance preservesColimit_discrete_tensorSheafRight
    (F : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    (Q : ℕ → _root_.SheafOfModules.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology ↥X) Osharp)) :
    Limits.PreservesColimit (Discrete.functor Q)
      (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
        (Opens.grothendieckTopology ↥X) Osharp F) :=
  (preservesColimitsOfShape_discrete_tensorSheafRight F).preservesColimit

/-- Tensoring on the right with a fixed factor preserves an `ℕ`-indexed coproduct. -/
instance preservesColimit_discrete_tensorSheafLeft
    (G : _root_.SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
    (Q : ℕ → _root_.SheafOfModules.{u, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (J := Opens.grothendieckTopology ↥X) Osharp)) :
    Limits.PreservesColimit (Discrete.functor Q)
      (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
        (Opens.grothendieckTopology ↥X) Osharp G) :=
  (preservesColimitsOfShape_discrete_tensorSheafLeft G).preservesColimit

variable (A' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E')
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E)
  (A'' : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology ↥X) E'')
  (f : E' ⟶ E) (g : E ⟶ E'') (hfg : f ≫ g = 0)
  (hS : (ShortComplex.mk f g hfg).Exact)

/-- The degreewise annihilators of a sheaf of modules have a coproduct, which is what `det` is.
The generic instance is instantiated by hand for the same reason
`SheafOfModules.TensorExteriorSymmetricAlgebras.hasCoproduct_exteriorAnnihilator` was stated:
the search for it no longer succeeds at the concrete site in this import closure. -/
instance hasCoproduct_exteriorAnnihilator_toSheafOfModules :
    Limits.HasCoproduct (fun j : ℕ => (A'.exteriorAnnihilator j).toSheafOfModules) :=
  A'.hasCoproduct_exteriorAnnihilator

/-- The same coproduct, with the sheaf of rings in the spelling
`Stacks.SheafOfModules.Tensor.ringSheaf`. The two spellings are reducibly
equal but not syntactically so, and instance search matches syntactically, so both are needed:
the determinant is defined over the first and the tensor-product functors of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorProductRightExact` are stated over the
second. -/
instance hasCoproduct_exteriorAnnihilator_underlying :
    Limits.HasCoproduct (C := _root_.SheafOfModules.{u, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (J := Opens.grothendieckTopology ↥X) Osharp))
      (fun j : ℕ => (A'.exteriorAnnihilator j).toSheafOfModules) :=
  A'.hasCoproduct_exteriorAnnihilator

/-- `det(E') ⊗ det(E'')ₘ` is the coproduct over `n` of the `det(E')ₙ ⊗ det(E'')ₘ`, because
tensoring preserves coproducts in its first variable
(`Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafLeft`). -/
noncomputable def isColimitCofanTensorAnnLeft (m : ℕ) :
    Limits.IsColimit (Limits.Cofan.mk
      ((Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
          (Opens.grothendieckTopology ↥X) Osharp
          (A''.exteriorAnnihilator m).toSheafOfModules).obj
        (∐ fun j : ℕ => (A'.exteriorAnnihilator j).toSheafOfModules))
      (fun n : ℕ =>
        (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
          (Opens.grothendieckTopology ↥X) Osharp
          (A''.exteriorAnnihilator m).toSheafOfModules).map
          (Limits.Sigma.ι (fun j : ℕ => (A'.exteriorAnnihilator j).toSheafOfModules) n))) :=
  Limits.isColimitOfHasCoproductOfPreservesColimit _ _

/-- **The comparison `det(E') ⊗ det(E'')ₘ ⟶ det(E)`**, assembled from the comparisons
`det(E')ₙ ⊗ det(E'')ₘ ⟶ det(E)ₙ₊ₘ` of
`Stacks.SheafOfModules.TopWedge.detSummandComparison` over the degrees `n`. -/
noncomputable def detTensorAnnComparison [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (m : ℕ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A'.determinant).obj
        ((A''.exteriorAnnihilator m).toSheafOfModules) ⟶ A.determinant :=
  Limits.Cofan.IsColimit.desc (isColimitCofanTensorAnnLeft A' A'' m)
    (fun n : ℕ => detSummandComparison A' A A'' f g hfg hS n m ≫
      A.determinantSummand (n + m))

/-- `det(E') ⊗ det(E'')` is the coproduct over `m` of the `det(E') ⊗ det(E'')ₘ`, because
tensoring preserves coproducts in its second variable
(`Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafRight`). -/
noncomputable def isColimitCofanTensorAnnRight :
    Limits.IsColimit (Limits.Cofan.mk
      ((Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
          (Opens.grothendieckTopology ↥X) Osharp A'.determinant).obj
        (∐ fun j : ℕ => (A''.exteriorAnnihilator j).toSheafOfModules))
      (fun m : ℕ =>
        (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
          (Opens.grothendieckTopology ↥X) Osharp A'.determinant).map
          (Limits.Sigma.ι (fun j : ℕ => (A''.exteriorAnnihilator j).toSheafOfModules) m))) :=
  Limits.isColimitOfHasCoproductOfPreservesColimit _ _

/-- **The canonical map `det(E') ⊗ det(E'') ⟶ det(E)` of [Stacks, Tag 0B38], for a short exact
sequence `0 → E' → E → E'' → 0` of sheaves of modules on a ringed space with `E'` and `E''`
finite locally free of NO PARTICULAR RANK.**

The determinant of [Stacks, Tag 0FJN] is the coproduct over the degrees of the degreewise
annihilators of the degree-one part of the exterior algebra, and the tensor product of sheaves of
modules preserves coproducts in each variable, so a map out of `det(E') ⊗ det(E'')` is the same
thing as a family of maps `det(E')ₙ ⊗ det(E'')ₘ ⟶ det(E)`. This is the family obtained from
`Stacks.SheafOfModules.TopWedge.detSummandComparison` followed by the inclusion of the
degree-`n+m` summand of `det(E)`.

That this map is an isomorphism is
`Stacks.SheafOfModules.TopWedge.isIso_determinantTensorDeterminantHom`, the isomorphism itself is
`Stacks.SheafOfModules.TopWedge.determinantTensorDeterminantIsoOfFiniteLocallyFree`, and the
wedge-and-lift formula pinning it is
`Stacks.SheafOfModules.TopWedge.detSummandComparison_ι_unit_wedge` — all three in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorShortExactIso`. -/
@[stacks 0B38 "the canonical MAP det(E')⊗det(E'')⟶det(E) in the GENERAL case, with NO \
constant-rank hypothesis"]
noncomputable def determinantTensorDeterminantHom [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor Osharp).obj A'.determinant).obj A''.determinant ⟶
        A.determinant :=
  Limits.Cofan.IsColimit.desc (isColimitCofanTensorAnnRight A' A'')
    (fun m : ℕ => detTensorAnnComparison A' A A'' f g hfg hS m)

/-- **The defining equation of the assembled comparison in the second variable**: restricted to
the degree-`m` summand of `det(E'')` it is
`Stacks.SheafOfModules.TopWedge.detTensorAnnComparison`. -/
theorem map_determinantSummand_comp_determinantTensorDeterminantHom [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (m : ℕ) :
    (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
          (Opens.grothendieckTopology ↥X) Osharp A'.determinant).map
        (Limits.Sigma.ι (fun j : ℕ => (A''.exteriorAnnihilator j).toSheafOfModules) m) ≫
      determinantTensorDeterminantHom A' A A'' f g hfg hS =
    detTensorAnnComparison A' A A'' f g hfg hS m :=
  Limits.Cofan.IsColimit.fac (isColimitCofanTensorAnnRight A' A'') _ m

/-- **The defining equation of the assembled comparison in the first variable**: restricted to
the degree-`n` summand of `det(E')` it is the comparison between summands followed by the
inclusion of the degree-`n+m` summand of `det(E)`. -/
theorem map_determinantSummand_comp_detTensorAnnComparison [Mono f] [Epi g]
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E']
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E''] (n m : ℕ) :
    (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
          (Opens.grothendieckTopology ↥X) Osharp
          (A''.exteriorAnnihilator m).toSheafOfModules).map
        (Limits.Sigma.ι (fun j : ℕ => (A'.exteriorAnnihilator j).toSheafOfModules) n) ≫
      detTensorAnnComparison A' A A'' f g hfg hS m =
    detSummandComparison A' A A'' f g hfg hS n m ≫ A.determinantSummand (n + m) :=
  Limits.Cofan.IsColimit.fac (isColimitCofanTensorAnnLeft A' A'' m) _ n

end Assembly

end Stacks.SheafOfModules.TopWedge

end
