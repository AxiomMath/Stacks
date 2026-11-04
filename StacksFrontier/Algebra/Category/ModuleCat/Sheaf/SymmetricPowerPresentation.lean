module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricStalkSheaf
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
public import StacksCore.Tactic.StacksAttribute

/-!
# Presenting the symmetric powers of a sheaf of modules on a space

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it and
`M₂ --q--> M₁ --p--> M ⟶ 0` a presentation of sheaves of `O♯`-modules. Stacks Tag 01CJ asserts
that in every degree `n ≥ 1` the sequence

`M₂ ⊗ Sym^{n-1}(M₁) ⟶ Symⁿ(M₁) ⟶ Symⁿ(M) ⟶ 0`

is exact, and the proof the source gives is a single citation to the module-level Tag 00DO. This
file carries out the transport of 00DO across the stalk, for the symmetric half of the tag:

* the stalk of `Symⁿ(M₁)` is identified with `Symⁿ` of the stalk, and the identification is
  computed on the germ of a product of degree-one generators. This is Tag 01CH, already on this
  branch as `SheafOfModules.symmetricPowerStalkEquiv` and
  `SheafOfModules.symmetricPowerStalkEquiv_germ_homogeneousProd`, and is reused rather than
  rebuilt;
* under that identification the second map of the sequence *is* `Symⁿ(pₓ)`
  (`symmetricPowerStalkEquiv_symDesc`);
* hence the second map is an **epimorphism** (`epi_symDesc_app`), which is the clause
  `⟶ 0` of the source's sequence, and its kernel on each stalk is the image of
  `m ⊗ y ↦ qₓ(m)·y` (`stalkMapL_symDesc_eq_zero_iff`), which is the kernel half of the
  source's exactness assertion.

## Main definitions

* `SheafOfModules.SymPresentation.valHom`: a morphism of sheaves of modules read as one of the
  underlying presheaves of modules over the presheaf of commutative rings — the shape
  `PresheafOfModules.stalkMapL` consumes.
* `SheafOfModules.SymPresentation.symDesc`: the homomorphism of sheaves of graded algebras
  induced by `p : M₁ ⟶ M` between a symmetric algebra of `M₁` and a symmetric algebra of `M`.
  Its degree-`n` component is the second map of the sequence of Tag 01CJ; it is
  `SheafOfModules.GradedAlgebra.IsUniversal.descComp`, the map of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences`.

## Main results

* `SheafOfModules.SymPresentation.epi_iff_surjective_stalkMapL`: epimorphy of a morphism of
  sheaves of modules on a space is surjectivity of its stalk maps, in the `CommRingCat`-linear
  spelling. This is `AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap` with the
  stalk map respelled; `stalkMap_apply` proves the two underlying functions agree by `rfl`.
* `SheafOfModules.SymPresentation.symmetricPowerStalkEquiv_symm_prod_ι`: the stalk identification
  of Tag 01CH read backwards. Since products of degree-one generators span the symmetric power of
  the stalk (`SymPow.ext_of_prod_ι`), this determines the identification.
* `SheafOfModules.SymPresentation.symmetricPowerStalkEquiv_symDesc`: **the second map of the
  sequence of Tag 01CJ is `Symⁿ` of the stalk of `p`.**
* `SheafOfModules.SymPresentation.epi_symDesc_app`: **the surjectivity clause of Tag 01CJ for
  symmetric powers.** If `p` is an epimorphism then so is `Symⁿ(p)`, in every degree.
* `SheafOfModules.SymPresentation.range_symMulMap_eq_ker_symMap`: **Tag 00DO on a stalk**, the
  symmetric half of `symmetric_power_presentation` applied to the stalk maps.
* `SheafOfModules.SymPresentation.stalkMapL_symDesc_eq_zero_iff`: **the kernel of the second map
  on each stalk** is the image of `m ⊗ y ↦ qₓ(m)·y`.

## Implementation notes

**What of Tag 01CJ is here and what is elsewhere.** The tag is the conjunction of two clauses:
the second map is surjective, and the sequence is exact at the middle term. The first is proved
here (`epi_symDesc_app`) and carries the tag with a clause comment. The second is proved in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPresentationExact`, as
`SheafOfModules.SymPresentation.symmetricPresentation_exact`, which carries the tag too; the
covering set for the symmetric half of Tag 01CJ is that pair. Neither subsumes the other:
`epi_symDesc_app` holds in every degree and needs no exactness hypothesis, while
`symmetricPresentation_exact` states the sequence of the source.

What this file contributes to the exactness clause is the identification of the *kernel* of the
second map on every stalk with the submodule `im(m ⊗ y ↦ qₓ(m)·y)` of `Sym^{k+1}(M₁ₓ)`
(`stalkMapL_symDesc_eq_zero_iff`), which together with the fact that exactness of a short complex
of sheaves of modules on a space is a stalkwise condition
(`AlgebraicGeometry.SheafOfModules.exact_iff_stalkFunctor_map_exact`) reduces the clause to the
matching identification of the *image* of the first map
`SheafOfModules.GradedAlgebra.generatorMul`. That last step needs the stalk of the sheafified
tensor product `M₂ ⊗ Sym^k(M₁)` and the compatibility of the multiplication
`A_1 ⊗ A_k ⟶ A_{1+k}` with the product of the symmetric algebra of the stalk, and is what
`SymmetricPresentationExact` supplies.

The stalk comparison it uses is `PresheafOfModules.tensorSheafStalkEquiv`, with its germ formula
`PresheafOfModules.tensorSheafStalkEquiv_tensorSheafGerm`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBifunctorStalk`. That comparison was, when
this file was written, available only for the bespoke tensor product of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace`
  (`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`) and not for
`Stacks.SheafOfModules.Tensor.sheafTensor`, which is the tensor product the complex of
`PowerPresentationSequences` is built from; it turned out to be a *transport* rather than a
construction, since the two tensor products are the same one, with
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf =
Stacks.SheafOfModules.Tensor.sheafTensor`
  holding by `rfl`.

The compatibility of `A.mul 1 k` with the product of the symmetric algebra of the stalk, together
with the `1 + k` versus `(k+1 : ℕ)` reindexing, is the remaining content, and it is where the work
was. Note `symmetricPowerStalkEquiv` is pinned down only on products of degree-one generators, so
that compatibility is proved on a germ tensored with a product of degree-one germs and extended by
`SymPow.ext_of_prod_ι`.

**The exterior half of Tag 01CJ is not here, and is no longer open.** It is the same argument,
transcribed in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact` as
`SheafOfModules.ExtPresentation.epi_extDesc_app` and
`SheafOfModules.ExtPresentation.exteriorPresentation_exact`. Several declarations of this file
were reused there verbatim rather than restated, because they mention no symmetry:
`SheafOfModules.SymPresentation.valHom`, `epi_iff_surjective_stalkMapL` and
`exists_common_germ`. The exterior-specific inputs are the exterior Tag 01CG
(`SheafOfModules.extPowCmp_eq_sheafifyUnit_comp`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerComparison`), the exterior Tag 01CH
(`PresheafOfModules.extPowStalkEquiv` with `PresheafOfModules.extPowStalkL_germ_ιMulti`, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk`, bundled for a sheaf of graded
algebras as `SheafOfModules.exteriorPowerStalkEquiv` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorStalkUngraded`),
`exterior_power_presentation` in place of `symmetric_power_presentation`, and
`ExteriorAlgebra.powExtₛₗ` in place of `SymPow.ext_of_prod_ι`.

**Two spellings of the stalk of the sheaf of rings.** `AlgebraicGeometry.SheafOfModules.stalkMap`
records linearity over the `RingCat`-valued stalk of the sheaf of rings, while
`PresheafOfModules.symPowStalkEquiv` and `PresheafOfModules.stalkMapL` record it over the
`CommRingCat`-valued stalk of the sheaf of commutative rings — the only one of the two carrying a
`CommRing` instance, hence the only one over which `SymmetricAlgebra` and `SymPow.symmetricPower`
can be formed. The two stalks are different types; the two module structures are on the same
abelian group and the two stalk maps are the same function, which `stalkMap_apply` proves by
`rfl`, so the crossing is confined to that lemma and to `epi_iff_surjective_stalkMapL`.

**The degree is always a variable.** No statement below writes a numeral degree. `A.piece (n : ℤ)`
for a variable `n` is opaque, but `SymPow.symmetricPower` sits over the reducible
`SymmetricAlgebra`, a `RingCon` quotient of `TensorAlgebra`, and with a numeral degree `whnf`
unfolds `symmetricPower (1 + 1)` through `Submodule.mul` and `Submodule.span` into that quotient,
which exhausts the heartbeat limit while elaborating the *statement*. The degree-`k+1` statements
of the last section keep `k` a variable.

**`rw` is avoided in favour of `congrArg` and `Eq.trans`.** Every proof below that touches
`symmetricPowerStalkEquiv` is written as a chain of `congrArg`/`Eq.trans` rather than with `rw` or
`simp`. The terms involved contain the stalk colimit and the symmetric-algebra quotient, and
`kabstract` — which `rw` uses to build its motive, and which calls `whnf` on subterms — exhausts
the heartbeat limit on them; the same goes for `rcases` on an existential when the goal is one of
these equations, which is why `exists_common_germ` is eliminated with `Exists.elim` and not with
`obtain`.

**Universes.** The single universe `u` carries the space, the sheaf of rings and the modules, and
the ring universe and the module universe of the graded algebras are equal. Both are inherited,
not chosen: Mathlib's module structure on the stalk of a presheaf of modules
(`Mathlib/Algebra/Category/ModuleCat/Stalk.lean`) exists only for `X : TopCat.{u}`,
`R : X.Presheaf CommRingCat.{u}` and modules in `u`, and
`SheafOfModules.symmetricPower_isSheafification` is stated for `GradedAlgebra.{w, w}`. Tag 01CJ is
stated in the equal-universe case, so nothing the source says is narrowed.

**The namespace.** Everything below lives in `SheafOfModules.SymPresentation` rather than in
`SheafOfModules`, so that the generic names `valHom` and `exists_common_germ` cannot collide with
a declaration of the same name elsewhere in the library. The stalk identification itself is taken
from `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricStalkSheaf`, which carries Tag 01CH
for the symmetric powers; nothing of it is rebuilt here.

## References

* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 00DO](https://stacks.math.columbia.edu/tag/00DO)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Sheaf

universe u

namespace SheafOfModules.SymPresentation

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}

/-! ### Stalk maps, and germs of a finite family of stalk elements -/

variable {N₁ N₂ : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}

/-- A morphism of sheaves of modules, read as a morphism of the underlying presheaves of modules
over the presheaf of commutative rings. This is the shape
`PresheafOfModules.stalkMapL` consumes. -/
noncomputable abbrev valHom (f : N₁ ⟶ N₂) :
    (PresheafOfModules.restrictScalars
        (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))).obj N₁.val ⟶
      (PresheafOfModules.restrictScalars
        (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))).obj N₂.val :=
  (PresheafOfModules.restrictScalars
    (toRingCatMap (Opens.grothendieckTopology ↥X) (𝟙 Osharp.obj))).map
      ((SheafOfModules.forget (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).map f)

/-- The stalk map of a morphism of sheaves of modules on a space, as computed in
`AlgebraicGeometry.SheafOfModules.stalkMap`, is `PresheafOfModules.stalkMapL` of the underlying
morphism of presheaves of modules. The two differ only in which ring the linearity is recorded
over: the `RingCat`-valued stalk of the sheaf of rings, or the `CommRingCat`-valued stalk of the
sheaf of commutative rings. The underlying functions agree on the nose. -/
theorem stalkMap_apply (f : N₁ ⟶ N₂) (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk N₁.val.presheaf x)) :
    (AlgebraicGeometry.SheafOfModules.stalkMap
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp) x f).hom t =
      PresheafOfModules.stalkMapL x (valHom f) t := rfl

/-- **Epimorphy of a morphism of sheaves of modules on a space is surjectivity of its stalk
maps**, with the stalk map in the `CommRingCat`-linear spelling of `stalkMapL`. -/
theorem epi_iff_surjective_stalkMapL (f : N₁ ⟶ N₂) :
    Epi f ↔ ∀ x : ↥X, Function.Surjective (PresheafOfModules.stalkMapL x (valHom f)) :=
  (AlgebraicGeometry.SheafOfModules.epi_iff_surjective_stalkMap f).trans
    (forall_congr' fun x => by
      exact ⟨fun h t => by obtain ⟨w, hw⟩ := h t; exact ⟨w, hw⟩,
        fun h t => by obtain ⟨w, hw⟩ := h t; exact ⟨w, hw⟩⟩)

/-- A finite family of germs at `x` is represented by sections over a single open neighbourhood
of `x`: the intersection of neighbourhoods on which each is defined. -/
theorem exists_common_germ (P : TopCat.Presheaf AddCommGrpCat.{u} X) (x : ↥X) (n : ℕ)
    (m : Fin n → ↑(TopCat.Presheaf.stalk P x)) :
    ∃ (U : Opens ↥X) (hx : x ∈ U) (s : Fin n → P.obj (op U)),
      ∀ i, TopCat.Presheaf.germ P U x hx (s i) = m i := by
  choose U hU t ht using fun i : Fin n => TopCat.Presheaf.exists_germ_eq P (m i)
  have hW : x ∈ (⨅ i, U i : Opens ↥X) := by
    have h : x ∈ (↑(⨅ i, U i) : Set ↥X) := by
      rw [Opens.coe_iInf]
      exact Set.mem_iInter.2 hU
    exact h
  refine ⟨⨅ i, U i, hW, fun i => P.map (homOfLE (iInf_le U i)).op (t i), fun i => ?_⟩
  exact (TopCat.Presheaf.germ_res_apply P (homOfLE (iInf_le U i)) x hW (t i)).trans (ht i)

/-! ### The stalk of a symmetric power -/

variable {M : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (A : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp))
  (gen : M ⟶ A.piece 1) (hA : GradedAlgebra.IsSymmetricAlgebra A gen)

/-- `SheafOfModules.symmetricPowerStalkEquiv` read backwards: the product of the degree-one
generators of `n` germs is the germ of the ordered product of the images of `n` representing
local sections. -/
theorem symmetricPowerStalkEquiv_symm_prod_ι (n : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (s : Fin n → M.val.obj (op U)) :
    (symmetricPowerStalkEquiv A gen hA n x).symm
        ⟨∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M.val.presheaf x)
            (TopCat.Presheaf.germ M.val.presheaf U x hx (s i)),
          SymmetricAlgebra.prod_ι_mem _ _⟩ =
      TopCat.Presheaf.germ (A.piece (n : ℤ)).val.presheaf U x hx
        (A.toPresheafGradedAlgebra.homogeneousProd (op U) n
          fun i => gen.val.app (op U) (s i)) :=
  ((symmetricPowerStalkEquiv A gen hA n x).symm_apply_eq).2
    (Subtype.ext (symmetricPowerStalkEquiv_germ_homogeneousProd A gen hA n x U hx s)).symm

/-! ### The second map of the presentation sequence -/

section Presentation

variable {M₁ : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  {A' B' : GradedAlgebra.{u, u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (ι : M₁ ⟶ A'.piece 1) (κ : M ⟶ B'.piece 1)
  (hA' : GradedAlgebra.IsSymmetricAlgebra A' ι) (hB' : GradedAlgebra.IsSymmetricAlgebra B' κ)
  (p : M₁ ⟶ M)

/-- The homomorphism of sheaves of graded algebras induced by `p : M₁ ⟶ M` between a symmetric
algebra of `M₁` and a symmetric algebra of `M`: the second map of the sequence of Tag 01CJ is its
degree-`n` component. -/
@[ega "II 4.1.2" "more general"]
noncomputable abbrev symDesc : GradedAlgebra.UnitalHom A' B' :=
  hA'.isUniversal.descComp p κ (GradedAlgebra.pairwiseCommutes_comp p hB'.1)

/-- In degree one, `symDesc ι κ hA' hB' p` sends the generator `ι y` of a local section `y` of
`M₁` to the generator `κ (p y)`. -/
theorem symDesc_app_one (U : (Opens ↥X)ᵒᵖ) (y : M₁.val.obj U) :
    ((symDesc ι κ hA' hB' p).app 1).val.app U (ι.val.app U y) =
      κ.val.app U (p.val.app U y) :=
  hom_congr_app_apply
    (hA'.isUniversal.descComp_extends p κ (GradedAlgebra.pairwiseCommutes_comp p hB'.1)) U y

/-- **The comparison homomorphism is `Symⁿ` of `p` on stalks, on a product of germs.** -/
theorem symmetricPowerStalkEquiv_symDesc_prod_germ (n : ℕ) (x : ↥X) (U : Opens ↥X) (hx : x ∈ U)
    (s : Fin n → M₁.val.obj (op U)) :
    symmetricPowerStalkEquiv B' κ hB' n x
        (PresheafOfModules.stalkMapL x (valHom ((symDesc ι κ hA' hB' p).app (n : ℤ)))
          ((symmetricPowerStalkEquiv A' ι hA' n x).symm
            ⟨∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
                ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)
                (TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i)),
              SymmetricAlgebra.prod_ι_mem _ _⟩)) =
      SymPow.symMap n (PresheafOfModules.stalkMapL x (valHom p))
        ⟨∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)
            (TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i)),
          SymmetricAlgebra.prod_ι_mem _ _⟩ := by
  have step1 : PresheafOfModules.stalkMapL x (valHom ((symDesc ι κ hA' hB' p).app (n : ℤ)))
        ((symmetricPowerStalkEquiv A' ι hA' n x).symm
          ⟨∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
              ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)
              (TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i)),
            SymmetricAlgebra.prod_ι_mem _ _⟩) =
      TopCat.Presheaf.germ (B'.piece (n : ℤ)).val.presheaf U x hx
        (B'.toPresheafGradedAlgebra.homogeneousProd (op U) n
          fun i => κ.val.app (op U) (p.val.app (op U) (s i))) := by
    refine Eq.trans (congrArg (PresheafOfModules.stalkMapL x
        (valHom ((symDesc ι κ hA' hB' p).app (n : ℤ))))
      (symmetricPowerStalkEquiv_symm_prod_ι A' ι hA' n x U hx s)) ?_
    refine Eq.trans (PresheafOfModules.stalkMapL_germ x _ U hx _) ?_
    refine congrArg (TopCat.Presheaf.germ (B'.piece (n : ℤ)).val.presheaf U x hx) ?_
    refine Eq.trans (GradedAlgebra.UnitalHom.app_homogeneousProd
      (symDesc ι κ hA' hB' p) (op U) n fun i => ι.val.app (op U) (s i)) ?_
    exact congrArg (B'.toPresheafGradedAlgebra.homogeneousProd (op U) n)
      (funext fun i => symDesc_app_one ι κ hA' hB' p (op U) (s i))
  refine Eq.trans (congrArg (symmetricPowerStalkEquiv B' κ hB' n x) step1) (Subtype.ext ?_)
  refine Eq.trans (symmetricPowerStalkEquiv_germ_homogeneousProd B' κ hB' n x U hx
    fun i => p.val.app (op U) (s i)) (Eq.symm ?_)
  refine Eq.trans (SymPow.symMap_coe n (PresheafOfModules.stalkMapL x (valHom p)) _) ?_
  refine Eq.trans (map_prod (SymPow.symAlgMap (PresheafOfModules.stalkMapL x (valHom p)))
    (fun i : Fin n => SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
      ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)
      (TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i))) Finset.univ) ?_
  refine Finset.prod_congr rfl fun i _ => Eq.trans (SymPow.symAlgMap_ι _ _) ?_
  exact congrArg _ (PresheafOfModules.stalkMapL_germ x (valHom p) U hx (s i))

/-- The same comparison on a product of arbitrary stalk elements: a finite family of germs is
represented by sections over one open neighbourhood. -/
theorem symmetricPowerStalkEquiv_symDesc_prod (n : ℕ) (x : ↥X)
    (m : Fin n → ↑(TopCat.Presheaf.stalk M₁.val.presheaf x)) :
    symmetricPowerStalkEquiv B' κ hB' n x
        (PresheafOfModules.stalkMapL x (valHom ((symDesc ι κ hA' hB' p).app (n : ℤ)))
          ((symmetricPowerStalkEquiv A' ι hA' n x).symm
            ⟨∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
                ↑(TopCat.Presheaf.stalk M₁.val.presheaf x) (m i),
              SymmetricAlgebra.prod_ι_mem _ _⟩)) =
      SymPow.symMap n (PresheafOfModules.stalkMapL x (valHom p))
        ⟨∏ i : Fin n, SymmetricAlgebra.ι ↑(TopCat.Presheaf.stalk Osharp.obj x)
            ↑(TopCat.Presheaf.stalk M₁.val.presheaf x) (m i),
          SymmetricAlgebra.prod_ι_mem _ _⟩ := by
  refine (exists_common_germ M₁.val.presheaf x n m).elim fun U hU =>
    hU.elim fun hx hU' => hU'.elim fun s hs => ?_
  have hm : m = fun i => TopCat.Presheaf.germ M₁.val.presheaf U x hx (s i) := (funext hs).symm
  subst hm
  exact symmetricPowerStalkEquiv_symDesc_prod_germ ι κ hA' hB' p n x U hx s

/-- **The comparison homomorphism is `Symⁿ` of `p` on stalks.** The stalk at `x` of the second map
of the sequence of Tag 01CJ is the `n`-th symmetric power of the stalk of `p`, read through the
identification `symmetricPowerStalkEquiv` of the stalks of the symmetric powers with the symmetric
powers of the stalks. -/
theorem symmetricPowerStalkEquiv_symDesc (n : ℕ) (x : ↥X)
    (t : ↑(TopCat.Presheaf.stalk (A'.piece (n : ℤ)).val.presheaf x)) :
    symmetricPowerStalkEquiv B' κ hB' n x
        (PresheafOfModules.stalkMapL x (valHom ((symDesc ι κ hA' hB' p).app (n : ℤ))) t) =
      SymPow.symMap n (PresheafOfModules.stalkMapL x (valHom p))
        (symmetricPowerStalkEquiv A' ι hA' n x t) := by
  have key : (symmetricPowerStalkEquiv B' κ hB' n x).toLinearMap.comp
        ((PresheafOfModules.stalkMapL x (valHom ((symDesc ι κ hA' hB' p).app (n : ℤ)))).comp
          (symmetricPowerStalkEquiv A' ι hA' n x).symm.toLinearMap) =
      SymPow.symMap n (PresheafOfModules.stalkMapL x (valHom p)) := by
    refine SymPow.ext_of_prod_ι fun m => ?_
    exact symmetricPowerStalkEquiv_symDesc_prod ι κ hA' hB' p n x m
  have h2 : symmetricPowerStalkEquiv B' κ hB' n x
        (PresheafOfModules.stalkMapL x (valHom ((symDesc ι κ hA' hB' p).app (n : ℤ)))
          ((symmetricPowerStalkEquiv A' ι hA' n x).symm
            (symmetricPowerStalkEquiv A' ι hA' n x t))) =
      SymPow.symMap n (PresheafOfModules.stalkMapL x (valHom p))
        (symmetricPowerStalkEquiv A' ι hA' n x t) :=
    DFunLike.congr_fun key (symmetricPowerStalkEquiv A' ι hA' n x t)
  exact Eq.trans (congrArg (fun z => symmetricPowerStalkEquiv B' κ hB' n x
    (PresheafOfModules.stalkMapL x (valHom ((symDesc ι κ hA' hB' p).app (n : ℤ))) z))
    ((symmetricPowerStalkEquiv A' ι hA' n x).symm_apply_apply t).symm) h2

/-- **The surjectivity clause of Stacks Tag 01CJ for symmetric powers.** If `p : M₁ ⟶ M` is an
epimorphism of sheaves of modules on a space, `A'` is a symmetric algebra of `M₁` and `B'` a
symmetric algebra of `M`, then the induced map `Symⁿ(M₁) ⟶ Symⁿ(M)` is an epimorphism in every
degree. This is the clause `⟶ 0` of the sequence Tag 01CJ asserts.

The hypothesis `n ≥ 1` of the source is not needed: the statement holds in degree `0` too, where
both powers are the structure sheaf. -/
@[stacks 01CJ "symmetric case, surjectivity clause: the second map of the sequence is an \
epimorphism, in every degree and with no exactness hypothesis. Exactness at the middle term is \
covered, by `SheafOfModules.SymPresentation.symmetricPresentation_exact` in \
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPresentationExact`, which carries that \
clause and states the sequence of the source. The exterior case is covered too, by \
`SheafOfModules.ExtPresentation.epi_extDesc_app` and \
`SheafOfModules.ExtPresentation.exteriorPresentation_exact` in \
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPresentationExact`; those four \
declarations are the tag's covering set."]
theorem epi_symDesc_app [Epi p] (n : ℕ) : Epi ((symDesc ι κ hA' hB' p).app (n : ℤ)) := by
  refine (epi_iff_surjective_stalkMapL ((symDesc ι κ hA' hB' p).app (n : ℤ))).2 fun x w => ?_
  have hp : Function.Surjective (PresheafOfModules.stalkMapL x (valHom p)) :=
    (epi_iff_surjective_stalkMapL p).1 inferInstance x
  obtain ⟨v, hv⟩ := SymPow.symMap_surjective n (PresheafOfModules.stalkMapL x (valHom p)) hp
    (symmetricPowerStalkEquiv B' κ hB' n x w)
  refine ⟨(symmetricPowerStalkEquiv A' ι hA' n x).symm v,
    (symmetricPowerStalkEquiv B' κ hB' n x).injective ?_⟩
  refine Eq.trans (symmetricPowerStalkEquiv_symDesc ι κ hA' hB' p n x _) ?_
  exact Eq.trans (congrArg (SymPow.symMap n (PresheafOfModules.stalkMapL x (valHom p)))
    ((symmetricPowerStalkEquiv A' ι hA' n x).apply_symm_apply v)) hv

/-! ### Stacks 00DO transported across the stalk -/

section Kernel

variable {M₂ : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (q : M₂ ⟶ M₁)

/-- **Stacks Tag 00DO on a stalk.** If the sequence of stalk modules
`M₂ₓ ⟶ M₁ₓ ⟶ Mₓ ⟶ 0` is exact, then the image of `m ⊗ y ↦ qₓ(m)·y` is the kernel of
`Sym^{k+1}(pₓ)`. This is `symmetric_power_presentation` — the symmetric half of Stacks 00DO —
applied to the stalk maps. -/
theorem range_symMulMap_eq_ker_symMap [Epi p] (k : ℕ) (x : ↥X)
    (hq : LinearMap.range (PresheafOfModules.stalkMapL x (valHom q)) =
      LinearMap.ker (PresheafOfModules.stalkMapL x (valHom p))) :
    LinearMap.range (SymPow.symMulMap k (PresheafOfModules.stalkMapL x (valHom q))) =
      LinearMap.ker (SymPow.symMap (k + 1) (PresheafOfModules.stalkMapL x (valHom p))) :=
  (symmetric_power_presentation (PresheafOfModules.stalkMapL x (valHom q))
    (PresheafOfModules.stalkMapL x (valHom p))
    ((epi_iff_surjective_stalkMapL p).1 inferInstance x) hq k).2

/-- **The kernel of the second map of the sequence of Tag 01CJ, on a stalk.** A germ of a local
section of `Sym^{k+1}(M₁)` is killed by the comparison homomorphism exactly when the
corresponding element of `Sym^{k+1}(M₁ₓ)` is a sum of products of a germ in the image of `qₓ`
with an element of `Sym^k(M₁ₓ)`.

This is the whole content of Stacks 01CJ for symmetric powers apart from the identification of
the *image* of the first map of the sequence with that submodule, which is
`SheafOfModules.SymPresentation.symmetricPowerStalkEquiv_symComplex_f` in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPresentationExact`; see the implementation
notes of this file. -/
theorem stalkMapL_symDesc_eq_zero_iff [Epi p] (k : ℕ) (x : ↥X)
    (hq : LinearMap.range (PresheafOfModules.stalkMapL x (valHom q)) =
      LinearMap.ker (PresheafOfModules.stalkMapL x (valHom p)))
    (t : ↑(TopCat.Presheaf.stalk (A'.piece ((k + 1 : ℕ) : ℤ)).val.presheaf x)) :
    PresheafOfModules.stalkMapL x
          (valHom ((symDesc ι κ hA' hB' p).app ((k + 1 : ℕ) : ℤ))) t = 0 ↔
      symmetricPowerStalkEquiv A' ι hA' (k + 1) x t ∈
        LinearMap.range (SymPow.symMulMap k (PresheafOfModules.stalkMapL x (valHom q))) := by
  have hker := range_symMulMap_eq_ker_symMap p q k x hq
  have hcomp := symmetricPowerStalkEquiv_symDesc ι κ hA' hB' p (k + 1) x t
  have hmem_iff := SetLike.ext_iff.mp hker (symmetricPowerStalkEquiv A' ι hA' (k + 1) x t)
  refine ⟨fun h0 => hmem_iff.mpr (LinearMap.mem_ker.2 (hcomp.symm.trans
    ((congrArg (symmetricPowerStalkEquiv B' κ hB' (k + 1) x) h0).trans (map_zero _)))),
    fun hmem => ?_⟩
  exact (symmetricPowerStalkEquiv B' κ hB' (k + 1) x).injective
    (hcomp.trans ((LinearMap.mem_ker.1 (hmem_iff.mp hmem)).trans (map_zero _).symm))

end Kernel

end Presentation

end SheafOfModules.SymPresentation

end
