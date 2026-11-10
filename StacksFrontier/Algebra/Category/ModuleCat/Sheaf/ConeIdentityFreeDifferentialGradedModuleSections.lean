module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeDescEquiv
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleClosedSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleConeHomotopy

/-!
# The universal property of the cone on the identity of a free differential graded module

Let `R` be a sheaf of rings on a site `(C, J)`, let `D` be a sheaf of differential graded
`R`-algebras and let `S` be a sheaf of graded sets. A homomorphism of right differential graded
modules out of the cone `C(𝟙_{D[S]})` is a pair: a homomorphism `β : D[S] ⟶ Q` and a right
`D`-linear degreewise family `α n : D[S]^{n+1} ⟶ Q^n` which is a null-homotopy of `β`. The second
datum determines the first — `β` is `d α + α d` — and, `D[S]` being free, the family `α` is
exactly a family of **arbitrary** local sections of `Q`, one of degree `i - 1` for every local
section of `S` of degree `i`. So

`Hom(C(𝟙_{D[S]}), Q) ≃ ∀ i, (degree-i sections of S ⟶ degree-(i-1) sections of Q)`,

naturally in `Q`. This is the free module's universal property with the closedness condition
dropped: the generator `s` of `C(𝟙_{D[S]})` in degree `|s| - 1` is not closed, its differential
being the generator of `D[S]`.

## Main definitions

* `SheafOfModules.coneIdentityFamily` is the family of homogeneous local sections of
  `gradedShiftDown Q` read off a homomorphism out of the cone, and
  `SheafOfModules.coneIdentityDesc` the homomorphism built from such a family.
* `SheafOfModules.coneIdentityFamilyEquiv`: **the universal property as a bijection** onto the
  families of homogeneous local sections of `gradedShiftDown Q` indexed by `S`.
* `SheafOfModules.coneIdentityHomEquiv`: **the same bijection in sheaves of sets** — onto the
  degreewise families of morphisms `degreeFiberSheaf S i ⟶ Q^{i-1}` of sheaves of sets, which is
  the shape a base change along a morphism of topoi runs through.

## Main results

* `SheafOfModules.inclusion_comp_eq_dgLiftHom`: **the cone's inclusion composed with a
  homomorphism out of the cone is the lift of the differentiated family.** This is the statement
  that the degree-`0` coordinate `β` is determined by the degree-`-1` coordinate `α`, read on the
  generators, and it is what the base change consumes to compare the cone's universal property
  with the free module's.
* `SheafOfModules.coneIdentityHomEquiv_comp`: **the bijection is natural in `Q`.**
* `SheafOfModules.freeDGModuleHomToClosed_comp_ι_inclusion`: **the closed generators the cone's
  inclusion carries are the differentials of the sections the cone's own universal property
  carries**, as an identity of morphisms of sheaves of sets. This is
  `inclusion_comp_eq_dgLiftHom` in the shape a base change along a morphism of topoi uses it,
  both sides being morphisms into the sheaf of all degree-`i` sections of `Q`.

## Implementation notes

The bijection is assembled rather than computed. Its cone half is
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedConeDescEquiv.lean`, which says a
homomorphism out of a cone is its two coordinates; its free half is
`SheafOfModules.liftHom_map_freeGenerator`, which says a homomorphism out of `D[S]` is the family
of generators it carries. The two are joined by
`SheafOfModules.DifferentialGradedModule.ofShiftDownHom` and `toShiftDownHom`, which identify the
degreewise families `α n : D[S]^{n+1} ⟶ Q^n` with the homomorphisms of graded modules
`D[S] ⟶ gradedShiftDown Q`; every transport between the degree `n + 1` at which a cone reads a
family and the degree `i - 1` at which `gradedShiftDown` stores it lives there and nowhere else.

The one computation is `inclusion_comp_eq_dgLiftHom`. It is the null-homotopy identity
`α n ≫ d + d ≫ α (n + 1) = β` evaluated on a canonical generator: the second term vanishes
because the generators of `D[S]` are closed, and what remains is `β(e_s) = d (α(e_s))`.

One universe `m` serves the sheaf of graded sets, the homogeneous pieces of the algebra and the
module sections, exactly as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeDifferentialGradedModuleClosedSections.lean`
and for the same reason: both sides of the bijection in sheaves of sets are morphisms in
`Sheaf J (Type m)`.

## References

* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- Two morphisms of sheaves of sets are equal if they agree on all local sections. -/
private theorem hom_ext_sections {X Y : Sheaf J (Type m)} {f g : X ⟶ Y}
    (h : ∀ (U : Cᵒᵖ) (x : X.obj.obj U), f.hom.app U x = g.hom.app U x) : f = g := by
  ext U x
  exact h U x

section ConeIdentity

variable [HasSheafify J (Type m)] [HasWeakSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  (S : SheafOfGradedSets.{m} J) (D : DifferentialGradedAlgebra.{t, m} R)
  (Q : DifferentialGradedModule.{t, m, m} D)

/-! ### Differentiating a family of sections of the shift down by one -/

/-- **The family of closed homogeneous generators obtained by differentiating a family of
sections of the shift down by one.** A local section of `S` of degree `i` carries a section of
`Q^{i-1}`; its differential is a section of `Q^i`, and it is closed because `d² = 0`. -/
noncomputable def dShiftDownFamily (μ : GradedGeneratorFamily S (gradedShiftDown Q)) :
    GradedGeneratorFamily S (GradedModule.ofDifferentialGraded Q) where
  app i U s hs := homSections (Q.complex.d (i - 1) i) U (μ.app i U s hs)
  naturality i {U V} r s hs hs' :=
    (homSections_naturality (Q.complex.d (i - 1) i) r (μ.app i U s hs)).trans
      (congrArg (fun z => homSections (Q.complex.d (i - 1) i) V z) (μ.naturality i r s hs hs'))

omit [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- The section of `Q^i` attached to `s` by `dShiftDownFamily` is the differential of the section
of `Q^{i-1}` attached to `s` by `μ`. -/
@[simp] theorem dShiftDownFamily_app (μ : GradedGeneratorFamily S (gradedShiftDown Q)) (i : ℤ)
    (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i) :
    (dShiftDownFamily S D Q μ).app i U s hs =
      homSections (Q.complex.d (i - 1) i) U (μ.app i U s hs) :=
  rfl

omit [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- Each section of the family `dShiftDownFamily μ` is closed, so the family lifts to a
homomorphism of *differential* graded modules. -/
theorem dShiftDownFamily_closed (μ : GradedGeneratorFamily S (gradedShiftDown Q)) (i : ℤ)
    (U : Cᵒᵖ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i) :
    homSections (Q.complex.d i (i + 1)) U ((dShiftDownFamily S D Q μ).app i U s hs) = 0 :=
  (homSections_comp (Q.complex.d (i - 1) i) (Q.complex.d i (i + 1)) U
        (μ.app i U s hs)).symm.trans
    ((homSections_congr (Q.complex.d_comp_d (i - 1) i (i + 1)) U (μ.app i U s hs)).trans
      (homSections_zero U _))

/-- The degree-`0` coordinate of the homomorphism out of the cone determined by a family: the
lift of the differentiated family. -/
noncomputable abbrev coneIdentityInclusionHom
    (μ : GradedGeneratorFamily S (gradedShiftDown Q)) : freeDGModule S D ⟶ Q :=
  dgLiftHom S D Q (dShiftDownFamily S D Q μ) (dShiftDownFamily_closed S D Q μ)

/-- **The homotopy carried by a family is a null-homotopy of the lift of the differentiated
family**, which is the cocycle condition a map out of the cone of the identity consumes. -/
theorem freeHomotopy_delta_dShiftDownFamily (μ : GradedGeneratorFamily S (gradedShiftDown Q))
    (n : ℤ) :
    freeHomotopy S D Q μ n ≫ Q.complex.d n (n + 1)
        + (freeDGModule S D).complex.d (n + 1) ((n + 1) + 1) ≫ freeHomotopy S D Q μ (n + 1)
      = (𝟙 (freeDGModule S D) :
            freeDGModule S D ⟶ freeDGModule S D).toHomologicalComplex.f (n + 1) ≫
          (coneIdentityInclusionHom S D Q μ).toHomologicalComplex.f (n + 1) :=
  (freeHomotopy_delta S D Q μ (dShiftDownFamily S D Q μ)
      (fun j V s hs =>
        (castHom_homSections_d Q.complex (j - 1) (degEqSubOneSucc j) V (μ.app j V s hs)).symm)
      n).trans
    (Category.id_comp _).symm

/-! ### The two passages -/

/-- **The homomorphism out of `C(𝟙_{D[S]})` determined by a family of homogeneous local sections
of the shift down by one of `Q`.** -/
noncomputable def coneIdentityDesc (μ : GradedGeneratorFamily S (gradedShiftDown Q)) :
    cone (𝟙 (freeDGModule S D)) ⟶ Q :=
  (conePackage (𝟙 (freeDGModule S D))).desc (coneIdentityInclusionHom S D Q μ)
    (freeHomotopy S D Q μ) (freeHomotopy_mul S D Q μ)
    (freeHomotopy_delta_dShiftDownFamily S D Q μ)

/-- The degree-`0` coordinate determined by a family sends the canonical generator attached to `s`
to the differential of the section the family attaches to `s`. -/
private theorem coneIdentityInclusionHom_generator
    (μ : GradedGeneratorFamily S (gradedShiftDown Q)) (i : ℤ) (U : Cᵒᵖ)
    (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i) :
    ((Hom.toHomologicalComplex (coneIdentityInclusionHom S D Q μ)).f i).val.app U
        (freeGeneratorSection D.toGradedAlgebra S i U s hs) =
      homSections (Q.complex.d (i - 1) i) U (μ.app i U s hs) :=
  dgLiftHom_generator S D Q (dShiftDownFamily S D Q μ) (dShiftDownFamily_closed S D Q μ) i U s hs

/-- **The family of homogeneous local sections of the shift down by one of `Q` read off a
homomorphism out of `C(𝟙_{D[S]})`**: the value of the homotopy the homomorphism restricts to on
the canonical generator. -/
noncomputable def coneIdentityFamily (h : cone (𝟙 (freeDGModule S D)) ⟶ Q) :
    GradedGeneratorFamily S (gradedShiftDown Q) :=
  (freeGenerator D.toGradedAlgebra S).map
    (toShiftDownHom (K := freeDGModule S D)
      ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom h)
      ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom_mul h))

/-- The section of `Q^{i-1}` attached to `s` by `coneIdentityFamily` is the image, under the
degree `i - 1` component of the homotopy determined by `h`, of the canonical generator attached
to `s`. -/
theorem coneIdentityFamily_app (h : cone (𝟙 (freeDGModule S D)) ⟶ Q) (i : ℤ) (U : Cᵒᵖ)
    (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i) :
    (coneIdentityFamily S D Q h).app i U s hs =
      homSections ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom h (i - 1)) U
        (castHom (freeDGModule S D).complex.X (degEqSubOneSucc i) U
          (freeGeneratorSection D.toGradedAlgebra S i U s hs)) :=
  (comp_val_app _ _ U _).trans
    (congrArg (fun w => homSections
        ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom h (i - 1)) U w)
      (homSections_eqToHom (freeDGModule S D).complex.X (degEqSubOneSucc i) U _))

/-! ### The degree-`0` coordinate is determined by the degree-`-1` one -/

/-- **The cone's inclusion composed with a homomorphism out of the cone is the lift of the
differentiated family.** The null-homotopy identity, evaluated on the canonical generator of
degree `i`: the term carrying the differential of `D[S]` vanishes, that generator being closed,
and what is left is the differential of the value of the homotopy on it. -/
theorem inclusion_comp_eq_dgLiftHom (h : cone (𝟙 (freeDGModule S D)) ⟶ Q) :
    (conePackage (𝟙 (freeDGModule S D))).inclusion ≫ h =
      coneIdentityInclusionHom S D Q (coneIdentityFamily S D Q h) := by
  refine dgHom_ext_generator S D Q fun i U s hs => ?_
  have hδ := congrArg (fun φ : (freeDGModule S D).complex.X ((i - 1) + 1) ⟶
        Q.complex.X ((i - 1) + 1) =>
      homSections φ U (castHom (freeDGModule S D).complex.X (degEqSubOneSucc i) U
        (freeGeneratorSection D.toGradedAlgebra S i U s hs)))
    ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom_delta h (i - 1))
  simp only [homSections_add, homSections_comp, id_f, homSections_id] at hδ
  have hzero : homSections ((freeDGModule S D).complex.d ((i - 1) + 1) (((i - 1) + 1) + 1)) U
      (castHom (freeDGModule S D).complex.X (degEqSubOneSucc i) U
        (freeGeneratorSection D.toGradedAlgebra S i U s hs)) = 0 :=
    (dgD_castHom (freeDGModule S D) (degEqSubOneSucc i)
          (show i + 1 = ((i - 1) + 1) + 1 by omega) U
          (freeGeneratorSection D.toGradedAlgebra S i U s hs)).trans
      ((congrArg (fun z => castHom (GradedModule.ofDifferentialGraded
              (freeDGModule S D)).piece (show i + 1 = ((i - 1) + 1) + 1 by omega) U z)
            (freeDGModule_d_freeGenerator S D i U s hs)).trans
        (Cofree.castHom_zero (GradedModule.ofDifferentialGraded (freeDGModule S D)).piece
          (show i + 1 = ((i - 1) + 1) + 1 by omega) U))
  rw [hzero, map_zero, add_zero] at hδ
  have hright : homSections ((Hom.toHomologicalComplex
        ((conePackage (𝟙 (freeDGModule S D))).inclusion ≫ h)).f ((i - 1) + 1)) U
      (castHom (freeDGModule S D).complex.X (degEqSubOneSucc i) U
        (freeGeneratorSection D.toGradedAlgebra S i U s hs)) =
      castHom Q.complex.X (degEqSubOneSucc i) U
        (homSections ((Hom.toHomologicalComplex
            ((conePackage (𝟙 (freeDGModule S D))).inclusion ≫ h)).f i) U
          (freeGeneratorSection D.toGradedAlgebra S i U s hs)) :=
    GradedModule.app_castHom (GradedModule.ofDifferentialGradedMap
      ((conePackage (𝟙 (freeDGModule S D))).inclusion ≫ h)) (degEqSubOneSucc i) U
      (freeGeneratorSection D.toGradedAlgebra S i U s hs)
  have key := ((castHom_homSections_d Q.complex (i - 1) (degEqSubOneSucc i) U
      (homSections ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom h (i - 1)) U
        (castHom (freeDGModule S D).complex.X (degEqSubOneSucc i) U
          (freeGeneratorSection D.toGradedAlgebra S i U s hs)))).trans hδ).trans hright
  have hgoalR : ((Hom.toHomologicalComplex
          (coneIdentityInclusionHom S D Q (coneIdentityFamily S D Q h))).f i).val.app U
        (freeGeneratorSection D.toGradedAlgebra S i U s hs) =
      homSections (Q.complex.d (i - 1) i) U
        (homSections ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom h (i - 1)) U
          (castHom (freeDGModule S D).complex.X (degEqSubOneSucc i) U
            (freeGeneratorSection D.toGradedAlgebra S i U s hs))) :=
    (coneIdentityInclusionHom_generator S D Q (coneIdentityFamily S D Q h) i U s hs).trans
      (congrArg (fun z => homSections (Q.complex.d (i - 1) i) U z)
        (coneIdentityFamily_app S D Q h i U s hs))
  exact (hgoalR.trans (eq_of_heq
    ((heq_castHom Q.complex.X (degEqSubOneSucc i) U _).symm.trans
      ((heq_of_eq key).trans (heq_castHom Q.complex.X (degEqSubOneSucc i) U _))))).symm

/-! ### The bijection -/

/-- **The universal property of `C(𝟙_{D[S]})`**: a homomorphism out of the cone on the identity
of the free differential graded module on `S` is exactly a family of homogeneous local sections
of the shift down by one of `Q` indexed by `S` — arbitrary sections, with no closedness
condition. -/
noncomputable def coneIdentityFamilyEquiv :
    (cone (𝟙 (freeDGModule S D)) ⟶ Q) ≃ GradedGeneratorFamily S (gradedShiftDown Q) where
  toFun h := coneIdentityFamily S D Q h
  invFun μ := coneIdentityDesc S D Q μ
  left_inv h := by
    have hΦ : liftHom D.toGradedAlgebra S (gradedShiftDown Q) (coneIdentityFamily S D Q h) =
        toShiftDownHom (K := freeDGModule S D)
          ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom h)
          ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom_mul h) :=
      liftHom_map_freeGenerator D.toGradedAlgebra S _
    have hα : freeHomotopy S D Q (coneIdentityFamily S D Q h) =
        (conePackage (𝟙 (freeDGModule S D))).homotopyOfHom h :=
      funext fun n => (congrArg (fun Ψ => ofShiftDownHom (K := freeDGModule S D) Ψ n) hΦ).trans
        (ofShiftDownHom_toShiftDownHom _ _ n)
    refine Eq.trans ?_ ((conePackage (𝟙 (freeDGModule S D))).desc_homotopyOfHom h)
    exact ConePackage.desc_congr _ (inclusion_comp_eq_dgLiftHom S D Q h).symm hα _ _ _ _
  right_inv μ := by
    have hΦ : toShiftDownHom (K := freeDGModule S D)
          ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom (coneIdentityDesc S D Q μ))
          ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom_mul
            (coneIdentityDesc S D Q μ)) =
        liftHom D.toGradedAlgebra S (gradedShiftDown Q) μ :=
      (toShiftDownHom_congr (K := freeDGModule S D)
          (funext fun n => (conePackage (𝟙 (freeDGModule S D))).homotopyOfHom_desc
            (coneIdentityInclusionHom S D Q μ) (freeHomotopy S D Q μ)
            (freeHomotopy_mul S D Q μ) (freeHomotopy_delta_dShiftDownFamily S D Q μ) n)
          ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom_mul (coneIdentityDesc S D Q μ))
          (ofShiftDownHom_mul (K := freeDGModule S D)
            (liftHom D.toGradedAlgebra S (gradedShiftDown Q) μ))).trans
        (toShiftDownHom_ofShiftDownHom (K := freeDGModule S D)
          (liftHom D.toGradedAlgebra S (gradedShiftDown Q) μ)
          (ofShiftDownHom_mul (K := freeDGModule S D)
            (liftHom D.toGradedAlgebra S (gradedShiftDown Q) μ)))
    refine GradedGeneratorFamily.ext fun i U s hs => ?_
    refine Eq.trans ?_ (liftHom_generator D.toGradedAlgebra S (gradedShiftDown Q) μ i U s hs)
    exact congrArg (fun Φ : GradedModule.Hom
        (GradedModule.ofDifferentialGraded (freeDGModule S D)) (gradedShiftDown Q) =>
      (Φ.app i).val.app U (freeGeneratorSection D.toGradedAlgebra S i U s hs)) hΦ

/-! ### The bijection in sheaves of sets -/

/-- The family of homogeneous local sections of the shift down by one of `Q` carried by a
degreewise family of morphisms of sheaves of sets. -/
noncomputable def shiftDownFamilyOfSections
    (F : ∀ i : ℤ, degreeFiberSheaf S i ⟶ (toSetSheaf R).obj (Q.complex.X (i - 1))) :
    GradedGeneratorFamily S (gradedShiftDown Q) where
  app i U s hs := (F i).hom.app U ⟨s, hs⟩
  naturality i {U _V} r s hs _hs' :=
    ((F i).hom.naturality_apply r (⟨s, hs⟩ : (degreeFiber S i).obj U)).symm

/-- The degreewise family of morphisms of sheaves of sets carried by a family of homogeneous
local sections of the shift down by one of `Q`. -/
noncomputable def sectionsOfShiftDownFamily (μ : GradedGeneratorFamily S (gradedShiftDown Q))
    (i : ℤ) : degreeFiberSheaf S i ⟶ (toSetSheaf R).obj (Q.complex.X (i - 1)) :=
  ⟨{ app U := ↾fun s => μ.app i U s.1 s.2
     naturality {U V} r := by
       ext s
       exact (μ.naturality i r s.1 s.2 (S.hasDegree_map r s.2)).symm }⟩

omit [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}] in
/-- The component of `sectionsOfShiftDownFamily μ i` at `U` sends a degree-`i` section `s` to the
section `μ.app i U s`. -/
@[simp] theorem sectionsOfShiftDownFamily_app
    (μ : GradedGeneratorFamily S (gradedShiftDown Q)) (i : ℤ) (U : Cᵒᵖ)
    (s : (degreeFiber S i).obj U) :
    (sectionsOfShiftDownFamily S D Q μ i).hom.app U s = μ.app i U s.1 s.2 :=
  rfl

/-- **The universal property of `C(𝟙_{D[S]})` in sheaves of sets**: a homomorphism of right
differential graded modules out of the cone on the identity of `D[S]` is exactly a family, one
for each degree `i`, of morphisms of sheaves of sets from the sheaf of degree-`i` local sections
of `S` to the sheaf of **all** degree-`(i-1)` local sections of `Q`. This is the universal
property `SheafOfModules.freeDGModuleHomEquiv` of `D[S]` with the closedness of the sections
dropped and the degree lowered by one. -/
noncomputable def coneIdentityHomEquiv :
    (cone (𝟙 (freeDGModule S D)) ⟶ Q) ≃
      ∀ i : ℤ, degreeFiberSheaf S i ⟶ (toSetSheaf R).obj (Q.complex.X (i - 1)) :=
  (coneIdentityFamilyEquiv S D Q).trans
    { toFun := sectionsOfShiftDownFamily S D Q
      invFun := shiftDownFamilyOfSections S D Q
      left_inv := fun μ => GradedGeneratorFamily.ext fun _ _ _ _ => rfl
      right_inv := fun F => funext fun i => by
        apply Sheaf.hom_ext
        apply NatTrans.ext
        funext U
        apply ConcreteCategory.hom_ext
        intro s
        rfl }

/-- The morphism of sheaves of sets `coneIdentityHomEquiv h i` sends a degree-`i` section `s` to
the section attached to `s` by `coneIdentityFamily h`. -/
theorem coneIdentityHomEquiv_apply (h : cone (𝟙 (freeDGModule S D)) ⟶ Q) (i : ℤ) (U : Cᵒᵖ)
    (s : (degreeFiber S i).obj U) :
    (coneIdentityHomEquiv S D Q h i).hom.app U s =
      (coneIdentityFamily S D Q h).app i U s.1 s.2 :=
  rfl

/-- **The bijection is natural in `Q`.** The family a homomorphism out of the cone restricts to
is natural in the target, so composing with `k : Q ⟶ Q'` composes the family with the degree
`i - 1` component of `k`. -/
theorem coneIdentityHomEquiv_comp {Q' : DifferentialGradedModule.{t, m, m} D}
    (h : cone (𝟙 (freeDGModule S D)) ⟶ Q) (k : Q ⟶ Q') (i : ℤ) :
    coneIdentityHomEquiv S D Q' (h ≫ k) i =
      coneIdentityHomEquiv S D Q h i ≫
        (toSetSheaf R).map (k.toHomologicalComplex.f (i - 1)) := by
  refine hom_ext_sections fun U s => ?_
  refine Eq.trans (coneIdentityFamily_app S D Q' (h ≫ k) i U s.1 s.2) ?_
  refine Eq.trans (congrArg (fun φ => homSections φ U _)
    ((conePackage (𝟙 (freeDGModule S D))).homotopyOfHom_comp h k (i - 1))) ?_
  exact congrArg (fun z => (k.toHomologicalComplex.f (i - 1)).val.app U z)
    (coneIdentityFamily_app S D Q h i U s.1 s.2).symm

/-- The inverse of the bijection is natural in `Q`: a family composed degreewise with the
degree-`(i-1)` component of `k` lifts to the homomorphism composed with `k`. -/
theorem coneIdentityHomEquiv_symm_comp
    (F : ∀ i : ℤ, degreeFiberSheaf S i ⟶ (toSetSheaf R).obj (Q.complex.X (i - 1)))
    {Q' : DifferentialGradedModule.{t, m, m} D} (k : Q ⟶ Q') :
    (coneIdentityHomEquiv S D Q').symm
        (fun i => F i ≫ (toSetSheaf R).map (k.toHomologicalComplex.f (i - 1))) =
      (coneIdentityHomEquiv S D Q).symm F ≫ k := by
  refine (coneIdentityHomEquiv S D Q').injective ?_
  rw [Equiv.apply_symm_apply]
  refine funext fun i => ?_
  rw [coneIdentityHomEquiv_comp, Equiv.apply_symm_apply]

/-- **The closed generators the cone's inclusion carries are the differentials of the sections
the cone's own universal property carries.** Both sides are morphisms of sheaves of sets into
the sheaf of all degree-`i` local sections of `Q`; this is `inclusion_comp_eq_dgLiftHom` read
there. -/
theorem freeDGModuleHomToClosed_comp_ι_inclusion (h : cone (𝟙 (freeDGModule S D)) ⟶ Q) (i : ℤ) :
    freeDGModuleHomToClosed S D Q ((conePackage (𝟙 (freeDGModule S D))).inclusion ≫ h) i ≫
        closedSectionι Q i =
      coneIdentityHomEquiv S D Q h i ≫ (toSetSheaf R).map (Q.complex.d (i - 1) i) := by
  refine hom_ext_sections fun U z => ?_
  change ((Hom.toHomologicalComplex
        ((conePackage (𝟙 (freeDGModule S D))).inclusion ≫ h)).f i).val.app U
      (freeGeneratorSection D.toGradedAlgebra S i U z.1 z.2) =
    homSections (Q.complex.d (i - 1) i) U ((coneIdentityFamily S D Q h).app i U z.1 z.2)
  refine Eq.trans (congrArg (fun φ : freeDGModule S D ⟶ Q =>
      ((Hom.toHomologicalComplex φ).f i).val.app U
        (freeGeneratorSection D.toGradedAlgebra S i U z.1 z.2))
    (inclusion_comp_eq_dgLiftHom S D Q h)) ?_
  exact coneIdentityInclusionHom_generator S D Q (coneIdentityFamily S D Q h) i U z.1 z.2

end ConeIdentity

end SheafOfModules

end
