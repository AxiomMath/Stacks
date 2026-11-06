module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleSingleDegree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleToposPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedRegularModuleUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodExtensionByZero
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPushforward

/-!
# The extension by zero of `A_U` is a good right differential graded module

Let `(C, O)` be a ringed site, let `A` be a sheaf of differential graded `O`-algebras on it, let
`U` be an object of `C` and let `j : (Sh(C/U), O_U) ⟶ (Sh(C), O)` be the localization morphism.
Write `A_U = j^*A` for the restriction of `A` to the slice site, taken as a right differential
graded `A_U`-module by its own multiplication. **The extension by zero `j_!A_U` is a good right
differential graded `A`-module**: it is flat as a graded module, it is K-flat, and both
properties survive every base change along a morphism of ringed topoi.

## Main definitions

* `SheafOfModules.closedOverEquiv`: the closed global degree-zero sections of `Q|_U` are the
  closed degree-zero sections of `Q` over `U`.
* `SheafOfModules.extensionByZeroRegularHomEquiv`: the universal property of `j_!A_U`, namely
  `Hom_A(j_!A_U, Q) ≃ Hom_{Sh}(h_U^#, Z_0 Q)`.
* `SheafOfModules.dgExtensionByZeroRegularIsoFree`: `j_!A_U` is the free differential graded
  `A`-module on the sheaf represented by `U`, placed in degree zero.

## Main results

* `SheafOfModules.extensionByZeroRegularHomEquiv_comp`: the universal property is natural.
* `SheafOfModules.IsGoodToposBaseChange.of_iso`: goodness, read at the source's own
  quantification, transports along an isomorphism of modules.
* `SheafOfModules.dgExtensionByZeroRegular_isGoodToposBaseChange`: **Tag 0FSB**, all three
  conditions of the definition of a good module.

## Implementation notes

**Which reading of goodness.** "Good" is the three-condition notion of Tag 0FSA. Condition (3)
quantifies over morphisms of *ringed topoi*, and the predicate at that quantification is
`SheafOfModules.IsGoodToposBaseChange` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleToposPullback.lean`,
where it is also what Tag 0FSG is registered at. Its conditions (1) and (2) are the library's
`SheafOfModules.RelativeTensor.IsGradedFlat` and `IsKFlat`; its condition (3) says that for every
second ringed topos `X`, every morphism of ringed topoi `f : X ⟶ Y`, every sheaf of differential
graded algebras `B` on `X` and every unital `ψ : A ⟶ f_*B`, a pullback of the module **exists**,
as an object corepresenting `Q ↦ Hom_A(P, f_{*,ψ}Q)`, and every such object is flat as a graded
module and K-flat. The site-indexed readings
`SheafOfModules.DifferentialGradedModule.IsGood`, `IsGoodCocontinuousBaseChange` and
`IsGoodSiteBaseChange` are untouched; their condition (3) has clauses along functors of sites
which induce no morphism of topoi, and that is a different quantification, not a weaker one.

**How condition (3) is obtained.** Not by the source's route. The source replaces the two topoi
by equivalent ones (Tag 03CR), reduces to a morphism coming from a continuous functor `u` of
sites, sets `U' = u(U)` and identifies `f^{-1}j_! = j'_!(f')^{-1}` (Tag 04J0) to conclude that
the pullback is again an extension by zero. What is done here instead is to identify `j_!A_U`
once and for all with a free module and then quote Tag 0FSG, whose condition (3) is already
proved at this quantification: the pullback of a free module is the free module on the inverse
image of its sheaf of graded sets, which needs no comparison of localizations. The two routes
prove the same statement; the one taken here is the one whose ingredients the development has.

**The identification.** `Hom_A(j_!A_U, Q)` is `Hom_{A_U}(A_U, Q|_U)` by the extension-restriction
adjunction of Tag 0FRW (`SheafOfModules.dgExtensionByZeroAdjunction`), which is
`Z^0(Q|_U)(C/U)` because the regular module is free on one closed generator of degree zero
(`SheafOfModules.DifferentialGradedModule.regularModuleHomEquiv`), which is `Z^0(Q)(U)` because
the slice site has a terminal object
(`Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv`), which is
`Hom_{Sh}(h_U^#, Z_0 Q)` because the sheafified representable corepresents evaluation
(`Stacks.Sheaves.GradedAlgebraPushforward.sheafSectionEquiv`). That is exactly the universal
property of the free differential graded module on `h_U^#` placed in degree zero
(`SheafOfModules.freeDGModuleConstDegHomEquiv`), so the two modules are isomorphic by
`SheafOfModules.DifferentialGradedModule.isoOfNatHomEquiv`.

That a sheaf of sets in a single degree has the free module one expects is not formal: the
degree-`i` fibre of `Stacks.constDeg F k` for `i ≠ k` is not empty — on an object covered by the
empty sieve every section has every degree — it is *initial*, which is the content of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedSetsConstantDegreeFiber.lean`.

**Conditions (1) and (2).** These are taken from
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodExtensionByZero.lean`, where they are proved by
the source's own argument for them — the identification `j_!A_U ⊗_A N = j_!(N_U)` of Tags 0FRB
and 0FRX together with the exactness of `j_!` (Tag 03DJ) and of restriction. The isomorphism of
this file would deliver them too, from Tag 0FSG's conditions (1) and (2); they are quoted from
there instead so that the registered theorem rests on the source's argument wherever the
development has it.

**Universes.** Site, sheaf of rings and modules all live in one universe, which is the discipline
of `GoodExtensionByZero.lean` and is forced there by Tag 03DJ. The second ringed topos of
condition (3) keeps its own two site universes.

## References

* [Stacks Project, Tag 0FSB](https://stacks.math.columbia.edu/tag/0FSB)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FRW](https://stacks.math.columbia.edu/tag/0FRW)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe u v₁ u₁

namespace SheafOfModules

open DifferentialGradedModule Stacks

section HomEquiv

/- Since Lean v4.35.0 instance search reaches `HasWeakSheafify J (Type u)` through the section
variable `[HasSheafify J (Type u)]` (via `instHasWeakSheafifyOfHasSheafify`), which would make
that variable a hypothesis of the declarations below. With the bridge erased here, the global
instance is found instead, as before the bump. -/
attribute [-instance] instHasWeakSheafifyOfHasSheafify

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify J (Type u)]
  (O : Sheaf J CommRingCat.{u}) (U : C)
  (A : DifferentialGradedAlgebra.{u, u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := J)) O))
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {O U A}

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J (Type u)]
  [(J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- A global degree-zero section of the restriction of `Q` to the slice site at `U` is closed
exactly when its value at `U` is. -/
theorem closedOver_iff (Q : DifferentialGradedModule.{u, u, u} A)
    (x : ((Q.over U).complex.X 0).sections) :
    (∀ V : (Over U)ᵒᵖ, ((Q.over U).complex.d 0 (0 + 1)).val.app V (x.eval V) = 0) ↔
      (Q.complex.d 0 (0 + 1)).val.app (op U)
        (Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv (Q.complex.X 0) U x) = 0 := by
  refine ⟨fun h => h (op (Over.mk (𝟙 U))), fun h V => ?_⟩
  have h0 : ((Q.over U).complex.d 0 (0 + 1)).val.app (op (Over.mk (𝟙 U)))
      (x.eval (op (Over.mk (𝟙 U)))) = 0 := h
  have hv : ((Q.over U).complex.X 0).val.map
        (Quiver.Hom.op (Over.homMk V.unop.hom (by simp) : V.unop ⟶ Over.mk (𝟙 U)))
        (x.eval (op (Over.mk (𝟙 U)))) = x.eval V :=
    x.property _
  refine Eq.trans
    (congrArg (fun z => ((Q.over U).complex.d 0 (0 + 1)).val.app V z) hv.symm) ?_
  rw [PresheafOfModules.naturality_apply, h0, map_zero]
  rfl

/-- **The closed global degree-zero sections of `Q|_U` are the closed degree-zero sections of
`Q` over `U`.** -/
noncomputable def closedOverEquiv (Q : DifferentialGradedModule.{u, u, u} A) :
    { x : ((Q.over U).complex.X 0).sections //
        ∀ V : (Over U)ᵒᵖ, ((Q.over U).complex.d 0 (0 + 1)).val.app V (x.eval V) = 0 } ≃
      (closedSectionSheaf Q 0).obj.obj (op U) :=
  Equiv.subtypeEquiv
    (Stacks.SheafOfModules.FiniteTypeKernel.sectionsOverEquiv (Q.complex.X 0) U)
    (closedOver_iff Q)

/-- **A homomorphism out of `j_!A_U` is a closed degree-zero section over `U`**, read as a
morphism out of the sheaf represented by `U`. -/
noncomputable def extensionByZeroRegularHomEquiv (Q : DifferentialGradedModule.{u, u, u} A) :
    (dgExtensionByZeroRegular.{u} O U A ⟶ Q) ≃
      ((presheafToSheaf J (Type u)).obj (yoneda.obj U) ⟶ closedSectionSheaf Q 0) :=
  (((dgExtensionByZeroAdjunction.{u} O U A).homEquiv
        (DifferentialGradedModule.regularModule (A.over U)) Q).trans
      ((regularModuleHomEquiv (Q.over U)).trans (closedOverEquiv Q))).trans
    (Stacks.Sheaves.GradedAlgebraPushforward.sheafSectionEquiv J (op U)
      (closedSectionSheaf Q 0))

omit [HasSheafify J (Type u)] [(J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify (J.over U) AddCommGrpCat.{u}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The bijection is natural in `Q`.** -/
theorem extensionByZeroRegularHomEquiv_comp {Q Q' : DifferentialGradedModule.{u, u, u} A}
    (k : Q ⟶ Q') (h : dgExtensionByZeroRegular.{u} O U A ⟶ Q) :
    extensionByZeroRegularHomEquiv Q' (h ≫ k) =
      extensionByZeroRegularHomEquiv Q h ≫ closedSectionMap k 0 := by
  have hnat := (dgExtensionByZeroAdjunction.{u} O U A).homEquiv_naturality_right h k
  refine (congrArg (Stacks.Sheaves.GradedAlgebraPushforward.sheafSectionEquiv J (op U)
    (closedSectionSheaf Q' 0)) ?_).trans
    (Stacks.Sheaves.GradedAlgebraPushforward.sheafSectionEquiv_comp J (op U)
      (closedSectionMap k 0) _)
  change closedOverEquiv Q' (regularModuleHomEquiv (Q'.over U) _) =
    (closedSectionMap k 0).hom.app (op U) (closedOverEquiv Q (regularModuleHomEquiv (Q.over U) _))
  erw [hnat]
  exact Subtype.ext rfl

/-- **`j_!A_U` is the free differential graded `A`-module on the sheaf represented by `U`, in
degree zero.** Both sides corepresent `Q ↦ Z^0(Q)(U)`. -/
noncomputable def dgExtensionByZeroRegularIsoFree :
    dgExtensionByZeroRegular.{u} O U A ≅
      freeDGModule (Stacks.constDeg.{u, u, u}
        ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) 0) A :=
  DifferentialGradedModule.isoOfNatHomEquiv
    (fun Q => (extensionByZeroRegularHomEquiv Q).trans
      (freeDGModuleConstDegHomEquiv
        ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) A 0 Q).symm)
    (fun {Q Q'} k h => by
      dsimp only [Equiv.trans_apply]
      rw [extensionByZeroRegularHomEquiv_comp]
      exact freeDGModuleConstDegHomEquiv_symm_comp
        ((presheafToSheaf J (Type u)).obj (yoneda.obj U)) A 0 Q k
        (extensionByZeroRegularHomEquiv Q h))

end HomEquiv

section Good

variable {Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify Y.J AddCommGrpCat.{u}]
  [HasSheafify Y.J (Type u)]
  {A : DifferentialGradedAlgebra.{u, u} (toRingCat Y.J Y.O)}

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

omit [HasSheafify Y.J (Type u)] in
/-- **Goodness at the source's own quantification transports along an isomorphism.** Flatness
and K-flatness do, and so does the existence of a pullback, the pullback being characterised by
corepresentability of a functor that depends on the module only through `coyoneda`. -/
theorem IsGoodToposBaseChange.of_iso {P P' : DifferentialGradedModule.{u, u, u} A} (e : P ≅ P')
    (h : IsGoodToposBaseChange.{u, v₁, u₁} P) : IsGoodToposBaseChange.{u, v₁, u₁} P' := by
  refine ⟨RelativeTensor.IsGradedFlat.of_iso
      (GradedModule.ofDifferentialGradedIso e) h.1,
    RelativeTensor.IsKFlat.of_iso e h.2.1, ?_⟩
  intro X _ _ _ _ _ _ f B ψ hψ
  obtain ⟨⟨T, ⟨c⟩⟩, hflat⟩ := h.2.2 f B ψ hψ
  exact ⟨⟨T, ⟨c.ofIso (Functor.isoWhiskerLeft _ (coyoneda.mapIso e.op)).symm⟩⟩,
    fun T' c' => hflat T' (c'.ofIso (Functor.isoWhiskerLeft _ (coyoneda.mapIso e.op)))⟩

variable (U : Y.C) (A)
  [(Y.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify (Y.J.over U) AddCommGrpCat.{u}]
  [(Y.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Tag 0FSB: the extension by zero `j_!A_U` of the restriction of `A` to the slice site at `U`
is a good right differential graded `A`-module.** It is flat as a graded module, it is K-flat,
and after every base change along a morphism of ringed topoi a pullback of it exists and every
pullback of it is again flat as a graded module and K-flat.

Conditions (1) and (2) are the two theorems of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodExtensionByZero.lean`, which run the source's
argument from Tags 0FRB, 0FRX and 0FSB. Condition (3) is Tag 0FSG's, read through the
identification of `j_!A_U` with the free differential graded module on the sheaf represented by
`U` in degree zero. -/
@[stacks 0FSB]
theorem dgExtensionByZeroRegular_isGoodToposBaseChange :
    IsGoodToposBaseChange.{u, v₁, u₁} (dgExtensionByZeroRegular.{u} Y.O U A) :=
  ⟨dgExtensionByZeroRegular_isGradedFlat.{u} Y.O U A,
    dgExtensionByZeroRegular_isKFlat.{u} Y.O U A,
    (IsGoodToposBaseChange.of_iso dgExtensionByZeroRegularIsoFree.symm
      (freeDGModule_isGoodToposBaseChange
        (Stacks.constDeg.{u, u, u}
          ((presheafToSheaf Y.J (Type u)).obj (yoneda.obj U)) 0))).2.2⟩

end Good

end SheafOfModules

end
