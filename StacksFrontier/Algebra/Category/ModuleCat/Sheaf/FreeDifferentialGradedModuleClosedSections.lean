module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedClosedSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedModuleLift

/-!
# The universal property of a free differential graded module, in sheaves of sets

Let `R` be a sheaf of rings on a site `(C, J)`, let `D` be a sheaf of differential graded
`R`-algebras and let `S` be a sheaf of graded sets. The canonical generators of the free
differential graded `D`-module `D[S]` are closed, so a homomorphism `D[S] ⟶ Q` of right
differential graded modules restricts, in each degree `i`, to a morphism of sheaves of sets from
the sheaf of degree-`i` local sections of `S` to the sheaf of *closed* degree-`i` local sections
of `Q`. **That restriction is a bijection**, and it is natural in `Q`.

Both sides of the bijection are now morphisms of sheaves of sets, which is the point: the
morphism out of a free module, a notion internal to differential graded modules, has been traded
for a family of morphisms of sheaves of sets, to which the inverse-image/direct-image adjunction
of a morphism of topoi applies degree by degree. This is the universal property in the shape the
base change of Tag 0FSG runs through — the source's `f^*A[S] = A'[f^{-1}S]`.

## Main definitions

* `SheafOfModules.freeGeneratorClosed` is the canonical generator of degree `i`, as a morphism of
  sheaves of sets into the closed degree-`i` sections of `D[S]`.
* `SheafOfModules.freeDGModuleHomToClosed` is the restriction of a homomorphism `D[S] ⟶ Q` to the
  generators, and `SheafOfModules.generatorFamilyOfClosed` is the passage back.
* `SheafOfModules.freeDGModuleHomEquiv`: **the universal property as a bijection**
  `(D[S] ⟶ Q) ≃ ∀ i, (degree-i sections of S ⟶ closed degree-i sections of Q)`.

## Main results

* `SheafOfModules.freeDGModuleHomToClosed_comp`: **the bijection is natural in `Q`.**
* `SheafOfModules.DifferentialGradedModule.isoOfNatHomEquiv`: two right differential graded
  modules with naturally bijective hom-sets out of them are isomorphic. This is the coYoneda
  lemma for right differential graded modules, written out because the hom-sets here are
  compared by a bijection rather than by an isomorphism of functors.
* `SheafOfModules.isoFreeDGModuleOfNatEquiv`: **a right differential graded module whose
  morphisms into every `Q` are naturally the families of closed generators indexed by `S` is the
  free module `D[S]`.** This is the identification that
  `SheafOfModules.freeDGModule_baseChange_of_free` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModuleBaseChange.lean` consumes.

## Implementation notes

The restriction map is **not** written out by hand: it is
`SheafOfModules.freeGeneratorClosed` followed by
`SheafOfModules.DifferentialGradedModule.closedSectionMap`, the functoriality of the sheaf of
closed sections. That is what makes naturality in `Q` a consequence of
`closedSectionMap_comp` rather than a second computation, and it is why the closedness of the
canonical generators (`SheafOfModules.freeDGModule_d_freeGenerator`) has to be checked only
once.

The inverse is `SheafOfModules.dgLiftHom`, and the two round trips are exactly the two halves of
Tag 0FSF's universal property: `SheafOfModules.dgLiftHom_generator` gives one, and
`SheafOfModules.freeGradedModule_hom_ext` — which holds because the pieces of `Q` are *sheaves* —
gives the other. Injectivity is transported through `GradedModule.ofDifferentialGradedMap`, whose
action on the degree-`n` component is the degree-`n` component of the original morphism, so no
information is lost in forgetting the differential.

One universe `m` serves the sheaf of graded sets, the homogeneous pieces of the algebra and the
module sections. That is forced, not chosen: both sides of the bijection are morphisms in
`Sheaf J (Type m)`, and `SheafOfModules.freeDGModule` on a `Stacks.SheafOfGradedSets.{w} J` over
a `DifferentialGradedAlgebra.{t, a}` has sections in `Type (max w a)`, so the sheaf of graded
sets and the algebra pieces must already share a universe for the statement to be writable. It
is the same shape `SheafOfModules.freeDGModule_baseChange_of_free` is stated at.

`HasSheafify J (Type m)` is carried rather than the weaker `HasWeakSheafify J (Type m)` that
`Stacks.SheafOfGradedSets` itself needs, for one reason only: `Stacks.degreeFiberSheaf` is stated
under it. Mathlib supplies it automatically at `Type (max u v)` for a site `C : Type u` with
`[Category.{v} C]`, so it is automatic where the source's sites live, and is an instance
hypothesis rather than a mathematical one elsewhere. No hypothesis is placed on any functor of
sites — there is none here — and no smallness anywhere.

## References

* [Stacks Project, Tag 0FSF](https://stacks.math.columbia.edu/tag/0FSF)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
* [Stacks Project, Tag 0FRI](https://stacks.math.columbia.edu/tag/0FRI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### The coYoneda lemma for right differential graded modules -/

namespace DifferentialGradedModule

variable {A : DifferentialGradedAlgebra.{t, m} R}

/-- **Two right differential graded modules with naturally bijective hom-sets out of them are
isomorphic.** This is the coYoneda lemma: the two inverse morphisms are the images of the two
identities, and the naturality of the bijection makes each round trip an identity. -/
noncomputable def isoOfNatHomEquiv {X Y : DifferentialGradedModule.{t, m, m} A}
    (e : ∀ Q : DifferentialGradedModule.{t, m, m} A, (X ⟶ Q) ≃ (Y ⟶ Q))
    (hnat : ∀ {Q Q' : DifferentialGradedModule.{t, m, m} A} (k : Q ⟶ Q') (h : X ⟶ Q),
      e Q' (h ≫ k) = e Q h ≫ k) : X ≅ Y where
  hom := (e Y).symm (𝟙 Y)
  inv := e X (𝟙 X)
  hom_inv_id := by
    refine (e X).injective ?_
    rw [hnat (e X (𝟙 X)) ((e Y).symm (𝟙 Y)), Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by simpa using (hnat ((e Y).symm (𝟙 Y)) (𝟙 X)).symm

end DifferentialGradedModule

/-! ### The universal property in sheaves of sets -/

section Universal

variable [HasSheafify J (Type m)] [HasWeakSheafify J AddCommGrpCat.{m}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  (S : SheafOfGradedSets.{m} J) (D : DifferentialGradedAlgebra.{t, m} R)

/-- **The canonical generator of degree `i`, as a morphism of sheaves of sets.** A local section
of `S` of degree `i` goes to its canonical generator in `D[S]`, which is closed. -/
noncomputable def freeGeneratorClosed (i : ℤ) :
    degreeFiberSheaf S i ⟶ closedSectionSheaf (freeDGModule S D) i :=
  ⟨{ app U := ↾fun s =>
        ⟨freeGeneratorSection D.toGradedAlgebra S i U s.1 s.2,
          freeDGModule_d_freeGenerator S D i U s.1 s.2⟩
     naturality {U V} r := by
       ext s
       exact Subtype.ext
         ((freeGenerator D.toGradedAlgebra S).naturality i r s.1 s.2
           (S.hasDegree_map r s.2)).symm }⟩

/-- The canonical generator of degree `i` sends a local section `s` of `S` to the section
`freeGeneratorSection` of `D[S]` it determines. -/
@[simp]
theorem freeGeneratorClosed_app (i : ℤ) (U : Cᵒᵖ) (s : (degreeFiber S i).obj U) :
    ((freeGeneratorClosed S D i).hom.app U s).1 =
      freeGeneratorSection D.toGradedAlgebra S i U s.1 s.2 :=
  rfl

variable (Q : DifferentialGradedModule.{t, m, m} D)

/-- **The restriction of a homomorphism `D[S] ⟶ Q` to the canonical generators**: in degree `i`,
a morphism of sheaves of sets from the degree-`i` sections of `S` to the closed degree-`i`
sections of `Q`. -/
noncomputable def freeDGModuleHomToClosed (h : freeDGModule S D ⟶ Q) (i : ℤ) :
    degreeFiberSheaf S i ⟶ closedSectionSheaf Q i :=
  freeGeneratorClosed S D i ≫ closedSectionMap h i

/-- The restriction of `h` to the generators sends a local section `s` of `S` of degree `i` to
the image under `h` of the canonical generator of `s`. -/
theorem freeDGModuleHomToClosed_app (h : freeDGModule S D ⟶ Q) (i : ℤ) (U : Cᵒᵖ)
    (s : (degreeFiber S i).obj U) :
    ((freeDGModuleHomToClosed S D Q h i).hom.app U s).1 =
      (h.toHomologicalComplex.f i).val.app U
        (freeGeneratorSection D.toGradedAlgebra S i U s.1 s.2) :=
  rfl

/-- **The restriction to the generators is natural in `Q`.** -/
theorem freeDGModuleHomToClosed_comp {Q' : DifferentialGradedModule.{t, m, m} D}
    (h : freeDGModule S D ⟶ Q) (k : Q ⟶ Q') (i : ℤ) :
    freeDGModuleHomToClosed S D Q' (h ≫ k) i =
      freeDGModuleHomToClosed S D Q h i ≫ closedSectionMap k i := by
  rw [freeDGModuleHomToClosed, freeDGModuleHomToClosed, closedSectionMap_comp,
    Category.assoc]

/-- A family of morphisms of sheaves of sets into the closed sections of `Q`, read as a family of
homogeneous generators of the right graded module underlying `Q`. -/
noncomputable def generatorFamilyOfClosed
    (F : ∀ i : ℤ, degreeFiberSheaf S i ⟶ closedSectionSheaf Q i) :
    GradedGeneratorFamily S (GradedModule.ofDifferentialGraded Q) where
  app i U s hs := ((F i).hom.app U ⟨s, hs⟩).1
  naturality i {U _V} r s hs _hs' :=
    (closedSection_map_val Q i r
        ((F i).hom.app U (⟨s, hs⟩ : (degreeFiber S i).obj U))).symm.trans
      (congrArg Subtype.val
        ((F i).hom.naturality_apply r (⟨s, hs⟩ : (degreeFiber S i).obj U))).symm

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
/-- The generators read off such a family are closed, which is what the family records. -/
theorem generatorFamilyOfClosed_closed
    (F : ∀ i : ℤ, degreeFiberSheaf S i ⟶ closedSectionSheaf Q i) (i : ℤ) (U : Cᵒᵖ)
    (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i) :
    homSections (Q.complex.d i (i + 1)) U
        ((generatorFamilyOfClosed S D Q F).app i U s hs) = 0 :=
  ((F i).hom.app U (⟨s, hs⟩ : (degreeFiber S i).obj U)).2

/-- **The universal property of `D[S]` in sheaves of sets.** A homomorphism of right differential
graded modules `D[S] ⟶ Q` is exactly a family, one for each degree `i`, of morphisms of sheaves
of sets from the sheaf of degree-`i` local sections of `S` to the sheaf of closed degree-`i`
local sections of `Q`. -/
noncomputable def freeDGModuleHomEquiv :
    (freeDGModule S D ⟶ Q) ≃
      ∀ i : ℤ, degreeFiberSheaf S i ⟶ closedSectionSheaf Q i where
  toFun h := freeDGModuleHomToClosed S D Q h
  invFun F := dgLiftHom S D Q (generatorFamilyOfClosed S D Q F)
    (generatorFamilyOfClosed_closed S D Q F)
  left_inv h := by
    have key : GradedModule.ofDifferentialGradedMap
          (dgLiftHom S D Q (generatorFamilyOfClosed S D Q (freeDGModuleHomToClosed S D Q h))
            (generatorFamilyOfClosed_closed S D Q (freeDGModuleHomToClosed S D Q h))) =
        GradedModule.ofDifferentialGradedMap h :=
      freeGradedModule_hom_ext D.toGradedAlgebra S (GradedModule.ofDifferentialGraded Q)
        fun n U s hs =>
          dgLiftHom_generator S D Q (generatorFamilyOfClosed S D Q
            (freeDGModuleHomToClosed S D Q h))
            (generatorFamilyOfClosed_closed S D Q (freeDGModuleHomToClosed S D Q h)) n U s hs
    exact DifferentialGradedModule.Hom.ext fun n =>
      congrArg (fun φ : GradedModule.Hom (GradedModule.ofDifferentialGraded (freeDGModule S D))
        (GradedModule.ofDifferentialGraded Q) => φ.app n) key
  right_inv F := by
    ext i U s
    exact Subtype.ext (dgLiftHom_generator S D Q (generatorFamilyOfClosed S D Q F)
      (generatorFamilyOfClosed_closed S D Q F) i U s.1 s.2)

/-- The universal property sends a homomorphism `h : D[S] ⟶ Q` to its restriction
`freeDGModuleHomToClosed` to the canonical generators. -/
@[simp]
theorem freeDGModuleHomEquiv_apply (h : freeDGModule S D ⟶ Q) :
    freeDGModuleHomEquiv S D Q h = freeDGModuleHomToClosed S D Q h :=
  rfl

/-- The inverse of the universal property is natural in `Q`: a family composed degreewise with
the closed sections of `k` lifts to the lift composed with `k`. -/
theorem freeDGModuleHomEquiv_symm_comp
    (F : ∀ i : ℤ, degreeFiberSheaf S i ⟶ closedSectionSheaf Q i)
    {Q' : DifferentialGradedModule.{t, m, m} D} (k : Q ⟶ Q') :
    (freeDGModuleHomEquiv S D Q').symm (fun i => F i ≫ closedSectionMap k i) =
      (freeDGModuleHomEquiv S D Q).symm F ≫ k := by
  refine (freeDGModuleHomEquiv S D Q').injective ?_
  rw [Equiv.apply_symm_apply, freeDGModuleHomEquiv_apply]
  refine funext fun i => ?_
  rw [freeDGModuleHomToClosed_comp, ← freeDGModuleHomEquiv_apply, Equiv.apply_symm_apply]

/-- **A right differential graded module whose morphisms into every `Q` are naturally the
families of closed generators indexed by `S` is the free module `D[S]`.** This is the
identification `f^*A[S] = A'[f^{-1}S]` in the form a base change supplies it: a natural
bijection of hom-sets, turned into an isomorphism by the coYoneda lemma. -/
noncomputable def isoFreeDGModuleOfNatEquiv (X : DifferentialGradedModule.{t, m, m} D)
    (e : ∀ Q : DifferentialGradedModule.{t, m, m} D,
      (X ⟶ Q) ≃ ∀ i : ℤ, degreeFiberSheaf S i ⟶ closedSectionSheaf Q i)
    (hnat : ∀ {Q Q' : DifferentialGradedModule.{t, m, m} D} (k : Q ⟶ Q') (h : X ⟶ Q) (i : ℤ),
      e Q' (h ≫ k) i = e Q h i ≫ closedSectionMap k i) :
    X ≅ freeDGModule S D :=
  DifferentialGradedModule.isoOfNatHomEquiv
    (fun Q => (e Q).trans (freeDGModuleHomEquiv S D Q).symm)
    fun {Q Q'} k h =>
      (congrArg (freeDGModuleHomEquiv S D Q').symm (funext fun i => hnat k h i)).trans
        (freeDGModuleHomEquiv_symm_comp S D Q (e Q h) k)

end Universal

end SheafOfModules

end
