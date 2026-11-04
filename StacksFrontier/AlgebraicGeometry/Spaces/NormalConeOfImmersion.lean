module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealization
public import StacksFrontier.AlgebraicGeometry.Constructions.GradedAlgebraToAlgebraSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSymmetricAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeSpecDirectImage

/-!
# The algebra sheaves of the normal cone and the normal bundle of algebraic spaces

Let `i : Z ⟶ X` be a morphism of algebraic spaces over a scheme `S`, with conormal algebra
`𝒞_{Z/X,*}` of Stacks 09RN and conormal sheaf `𝒞_{Z/X} = 𝒞_{Z/X,1}` its degree-one piece.
**Stacks 09RU** defines, for an immersion, the normal cone
`C_ZX = \underline{Spec}_Z(𝒞_{Z/X,*})` and the normal bundle
`N_ZX = \underline{Spec}_Z(Sym(𝒞_{Z/X}))` as relative spectra, in the sense of Stacks 081W, of
two quasi-coherent algebras. This file builds those two algebras as sheaves of commutative
`𝒪_Z`-algebras: the ungraded realization of the **graded conormal algebra**, and the symmetric
algebra on the **single sheaf** `𝒞_{Z/X}`. The relative spectra themselves, for an immersion,
are `AlgebraicGeometry.Space.immersionNormalCone` and
`AlgebraicGeometry.Space.immersionNormalBundle` of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalConeRelativeSpectrum`.

## Main definitions

* `AlgebraicGeometry.Space.symmetricAlgebra`, with `symmetricAlgebraGen`: the symmetric algebra
  of a sheaf of modules on the small étale site of an algebraic space, as a sheaf of graded
  algebras with its degree-one generator.
* `AlgebraicGeometry.Space.gradedAlgebraSheaf`: a sheaf of graded `𝒪_W`-algebras with
  commutative homogeneous multiplication, as a sheaf of commutative `𝒪_W`-algebras — the shape
  a relative spectrum takes as input.
* `AlgebraicGeometry.Space.conormalAlgebraPieceOne`: `𝒞_{Z/X}`, the degree-one piece of the
  conormal algebra, and `conormalAlgebraSheaf`, `conormalSymmetricAlgebraSheaf`: `𝒞_{Z/X,*}`
  and `Sym(𝒞_{Z/X})` as sheaves of commutative algebras.

## Main results

* `AlgebraicGeometry.Space.isSymmetricAlgebra_symmetricAlgebra`: the symmetric algebra of a
  sheaf of modules on an algebraic space is universal, and
  `symmetricAlgebra_mul_comm`: its homogeneous multiplication is commutative in every pair of
  integer degrees.

## Implementation notes

### Commutativity of the conormal algebra

`AlgebraicGeometry.Space.conormalAlgebraSheaf` takes commutativity of the conormal algebra in
every pair of integer degrees as its argument `hc`, since the ungraded realization needs all
pairs: its sections mix degrees. It is supplied by
`AlgebraicGeometry.Space.isCommutative_conormalAlgebra`, which is downstream of this file.
`Sym(𝒞_{Z/X})` needs no such argument: `AlgebraicGeometry.Space.symmetricAlgebra_mul_comm` holds
in every pair of degrees. Quasi-coherence of the two algebras, which a relative spectrum also
needs, is likewise proved downstream, for an immersion, in
`StacksFrontier.AlgebraicGeometry.Spaces.ConormalAlgebraQuasicoherent` and
`StacksFrontier.AlgebraicGeometry.Spaces.NormalConeRelativeSpectrum`.

### Two universe-general restatements

`Stacks.CommRingSheaf.sheaf` and `Stacks.GradedAlgebra.mul_comm_total` are stated for a site
`C : Type u` with `Category.{u} C`. The small étale site of an algebraic space is
`SmallEtale B S hS F : Type (u + 1)` with morphisms in `Type u`, so neither applies here.
`AlgebraicGeometry.Space.commRingSheafOfMulComm` and
`AlgebraicGeometry.Space.mulComm_ungradedSheaf` restate them with the two site universes
independent; the arguments are unchanged, and the ring-level lift
`Stacks.CommRingSheaf.ofRingCat`, which mentions no site, is reused rather than repeated.

### The four named instance arguments

`AlgebraicGeometry.Space.symmetricAlgebra` passes the instance arguments of
`PresheafOfModules.symmetricAlgebraSheafify` explicitly, as
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra` does: all four are `inferInstance` on the
small étale site, but instance search does not find them while the structure map is still a
metavariable, so they are named and supplied positionally.

## References

* [Stacks Project, Tag 09RU](https://stacks.math.columbia.edu/tag/09RU)
* [Stacks Project, Tag 09RN](https://stacks.math.columbia.edu/tag/09RN)
* [Stacks Project, Tag 09RQ](https://stacks.math.columbia.edu/tag/09RQ)
* [Stacks Project, Tag 081W](https://stacks.math.columbia.edu/tag/081W)
* [Stacks Project, Tag 0636](https://stacks.math.columbia.edu/tag/0636)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace AlgebraicGeometry.Space

/-! ### A sheaf of rings with commuting sections, as a sheaf of commutative rings

A universe-general restatement of `Stacks.CommRingSheaf.presheaf`, `isSheaf_presheaf` and
`sheaf`; see the implementation notes. -/

section CommRingSheaf

variable {C : Type u} [Category.{v} C]

/-- A presheaf of rings whose sections commute, as a presheaf of commutative rings, for a site
whose morphisms live in a universe of their own. -/
def commRingPresheafOfMulComm (P : Cᵒᵖ ⥤ RingCat.{w})
    (h : ∀ (W : Cᵒᵖ) (a b : P.obj W), a * b = b * a) : Cᵒᵖ ⥤ CommRingCat.{w} where
  obj W := Stacks.CommRingSheaf.ofRingCat (P.obj W) (h W)
  map {W W'} f := Stacks.CommRingSheaf.ofRingCatHom (h W) (h W') (P.map f)
  map_id W := by ext x; exact congrArg (fun g => RingCat.Hom.hom g x) (P.map_id W)
  map_comp f g := by ext x; exact congrArg (fun g => RingCat.Hom.hom g x) (P.map_comp f g)

/-- A presheaf of rings whose sections commute is a sheaf of commutative rings as soon as it is
a sheaf of rings: forgetting commutativity returns the presheaf one started with, and
`forget₂ CommRingCat RingCat` is fully faithful, hence reflects limits. -/
theorem isSheaf_commRingPresheafOfMulComm (J : GrothendieckTopology C) (P : Cᵒᵖ ⥤ RingCat.{w})
    (h : ∀ (W : Cᵒᵖ) (a b : P.obj W), a * b = b * a) (hP : Presheaf.IsSheaf J P) :
    Presheaf.IsSheaf J (commRingPresheafOfMulComm P h) := by
  exact Presheaf.isSheaf_of_isSheaf_comp J (commRingPresheafOfMulComm P h)
    (forget₂ CommRingCat.{w} RingCat.{w}) hP

/-- **A sheaf of rings whose sections commute, as a sheaf of commutative rings.** -/
def commRingSheafOfMulComm {J : GrothendieckTopology C} (T : Sheaf J RingCat.{w})
    (h : ∀ (W : Cᵒᵖ) (a b : T.obj.obj W), a * b = b * a) : Sheaf J CommRingCat.{w} :=
  ⟨commRingPresheafOfMulComm T.obj h, isSheaf_commRingPresheafOfMulComm J T.obj h T.property⟩

end CommRingSheaf

/-! ### Commutativity of the ungraded realization

A universe-general restatement of `Stacks.GradedAlgebra.incl_eq_incl_of_heq`,
`Stacks.GradedAlgebra.mul_comm_total` and
`SheafOfModules.GradedAlgebra.mul_comm_ungradedSheaf`; see the implementation notes. -/

section MulComm

variable {C : Type u} [Category.{v} C]

/-- Two homogeneous local sections of equal degree which are heterogeneously equal have the same
image in the ungraded realization. -/
theorem inclEqIncl_of_heq {R : Cᵒᵖ ⥤ RingCat.{t}} {ι : Type} [DecidableEq ι] [AddMonoid ι]
    {P : ι → PresheafOfModules.{w} R} (A : Stacks.GradedAlgebra P) {W : Cᵒᵖ} {i j : ι}
    (hij : i = j) {x : (P i).obj W} {y : (P j).obj W} (hxy : HEq x y) :
    A.incl i x = A.incl j y := by
  subst hij
  rw [eq_of_heq hxy]

/-- **Graded commutativity makes the ungraded realization commutative over each object of the
site.** The multiplication of the direct sum of the homogeneous components is determined on
homogeneous sections by the graded multiplication and is biadditive. -/
theorem mulComm_total {R : Cᵒᵖ ⥤ RingCat.{t}} {ι : Type} [DecidableEq ι] [AddMonoid ι]
    {P : ι → PresheafOfModules.{w} R} (A : Stacks.GradedAlgebra P)
    (hadd : ∀ i j : ι, i + j = j + i)
    (hc : ∀ (i j : ι) (W : Cᵒᵖ) (x : (P i).obj W) (y : (P j).obj W),
      HEq ((A.mul i j).app W x y) ((A.mul j i).app W y x))
    (W : Cᵒᵖ) (a b : A.Total W) : a * b = b * a := by
  induction a using A.incl_induction with
  | incl i x =>
    induction b using A.incl_induction with
    | incl j y =>
      rw [A.incl_mul_incl, A.incl_mul_incl]
      exact inclEqIncl_of_heq A (hadd i j) (hc i j W x y)
    | _ => simp_all [mul_add, add_mul]
  | _ => simp_all [mul_add, add_mul]

/-- **The ungraded realization of a sheaf of graded algebras with commutative homogeneous
multiplication has commuting sections.** -/
theorem mulComm_ungradedSheaf {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [HasSheafify J RingCat.{w}] [J.WEqualsLocallyBijective RingCat.{w}]
    [J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
    (A : SheafOfModules.GradedAlgebra.{w, w} R)
    (hc : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (W : Cᵒᵖ) (s t : A.ungradedSheaf.obj.obj W) : s * t = t * s :=
  A.toPresheafGradedAlgebra.mul_comm_totalSheaf J
    (mulComm_total A.toPresheafGradedAlgebra (fun i j => add_comm i j) hc) W s t

end MulComm

/-! ### The universal property of a symmetric algebra along an isomorphism

A universe-general restatement of `SheafOfModules.GradedAlgebra.isSymmetricAlgebra_of_iso_source`;
see the implementation notes. -/

section IsoSource

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  {M N : SheafOfModules.{w} R} {A : SheafOfModules.GradedAlgebra.{w, w} R}

/-- **The universal property of the symmetric algebra, transported along an isomorphism of the
generating sheaf of modules.** If `A` with `ι : M ⟶ A.piece 1` is the symmetric algebra of `M`
and `e : M ≅ N`, then `A` with `e.inv ≫ ι` is the symmetric algebra of `N`. -/
theorem isSymmetricAlgebra_of_isoSource (e : M ≅ N) {ι : M ⟶ A.piece 1}
    (h : SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A ι) :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra A (e.inv ≫ ι) := by
  refine ⟨fun U s u => h.1 U (e.inv.val.app U s) (e.inv.val.app U u), fun T κ hκ => ?_⟩
  obtain ⟨g, hg, hgu⟩ := h.2 T (e.hom ≫ κ)
    fun U s u => hκ U (e.hom.val.app U s) (e.hom.val.app U u)
  refine ⟨g, ?_, fun h' hh' => hgu h' ?_⟩
  · change (e.inv ≫ ι) ≫ g.app 1 = κ
    rw [Category.assoc, hg, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  · have hh'' : (e.inv ≫ ι) ≫ h'.app 1 = κ := hh'
    change ι ≫ h'.app 1 = e.hom ≫ κ
    rw [← hh'', ← Category.assoc, ← Category.assoc, e.hom_inv_id, Category.id_comp]

end IsoSource

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### A sheaf of graded algebras as an algebra sheaf on an algebraic space -/

/-- **A sheaf of graded `𝒪_W`-algebras with commutative homogeneous multiplication, as a sheaf
of commutative `𝒪_W`-algebras.** Its sheaf of rings is the ungraded realization
`SheafOfModules.GradedAlgebra.ungradedSheaf` and its structure map is
`SheafOfModules.GradedAlgebra.ungradedStructureMap`; quasi-coherence is not asserted. This is
the shape `AlgebraicGeometry.Space.relativeSpec` takes as input. -/
def gradedAlgebraSheaf (W : AlgebraicSpaces B S hS)
    (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS W))
    (hc : ∀ (i j : ℤ) (V : (SmallEtale B S hS W.1)ᵒᵖ) (a : (A.piece i).val.obj V)
      (b : (A.piece j).val.obj V), HEq ((A.mul i j).app V a b) ((A.mul j i).app V b a)) :
    AlgebraSheaf.{u, u} B S hS W.1 W.2 where
  right := commRingSheafOfMulComm A.ungradedSheaf (mulComm_ungradedSheaf A hc)
  algebraMap V := (A.ungradedStructureMap.hom.app V).hom
  algebraMap_natural f r :=
    (ConcreteCategory.congr_hom (A.ungradedStructureMap.hom.naturality f) r).symm

/-! ### The symmetric algebra of a sheaf of modules on an algebraic space

The four instance arguments of `PresheafOfModules.symmetricAlgebraSheafify`, named so that they
can be supplied positionally; see the implementation notes. -/

section SymmetricAlgebra

/-- The structure map of the small étale site is locally injective, being the identity. -/
theorem isLocallyInjective_id_structureRingSheaf (W : AlgebraicSpaces B S hS) :
    Presheaf.IsLocallyInjective (SmallEtale.topology B S hS W.1)
      (𝟙 ((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :=
  inferInstance

/-- The structure map of the small étale site is locally surjective, being the identity. -/
theorem isLocallySurjective_id_structureRingSheaf (W : AlgebraicSpaces B S hS) :
    Presheaf.IsLocallySurjective (SmallEtale.topology B S hS W.1)
      (𝟙 ((structureSheaf B S hS W.1 W.2).obj ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :=
  inferInstance

/-- The local equivalences of presheaves of abelian groups on the small étale site are the
locally bijective morphisms. -/
theorem wEqualsLocallyBijective_smallEtale (W : AlgebraicSpaces B S hS) :
    (SmallEtale.topology B S hS W.1).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstance

/-- Presheaves of abelian groups on the small étale site admit sheafification. -/
theorem hasWeakSheafify_smallEtale (W : AlgebraicSpaces B S hS) :
    HasWeakSheafify (SmallEtale.topology B S hS W.1) AddCommGrpCat.{u} :=
  inferInstance

variable (W : AlgebraicSpaces B S hS) (F : SheafOfModules.{u} (structureRingSheaf B S hS W))

/-- **The symmetric algebra `Sym(F)` of a sheaf of modules on an algebraic space**, as a sheaf
of graded algebras over the structure sheaf of its small étale site: the degreewise
sheafification of the presheaf `U ↦ Symⁿ_{𝒪_W(U)}(F(U))`. -/
def symmetricAlgebra : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS W) :=
  @PresheafOfModules.symmetricAlgebraSheafify.{u, u + 1, u, u} _ _
    (SmallEtale.topology B S hS W.1) (structureSheaf B S hS W.1 W.2).obj
    (structureRingSheaf B S hS W) (𝟙 _) (isLocallyInjective_id_structureRingSheaf B S hS W)
    (isLocallySurjective_id_structureRingSheaf B S hS W)
    (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W) F.val

/-- The sheafification of `F` along the identity structure map is `F`: the counit of
`PresheafOfModules.sheafificationAdjunction` is an isomorphism and `F` is already a sheaf. This
is what lets the degree-one generator of `Sym(F)` be taken out of `F` itself. -/
def symmetricAlgebraSheafificationIso :
    (PresheafOfModules.sheafification.{u}
        (α := 𝟙 (structureRingSheaf B S hS W).obj)).obj F.val ≅ F :=
  (asIso (PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 (structureRingSheaf B S hS W).obj)).counit).app F

/-- **The degree-one generator of `Sym(F)`**, out of `F` itself. -/
def symmetricAlgebraGen : F ⟶ (symmetricAlgebra B S hS W F).piece 1 :=
  (symmetricAlgebraSheafificationIso B S hS W F).inv ≫
    @PresheafOfModules.symmetricAlgebraSheafifyGen.{u, u + 1, u, u} _ _
      (SmallEtale.topology B S hS W.1) (structureSheaf B S hS W.1 W.2).obj
      (structureRingSheaf B S hS W) (𝟙 _) (isLocallyInjective_id_structureRingSheaf B S hS W)
      (isLocallySurjective_id_structureRingSheaf B S hS W)
      (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W) F.val

/-- **`Sym(F)` is the symmetric algebra of `F`**: it is universal among sheaves of graded
`𝒪_W`-algebras carrying a pairwise-commuting degree-one generator of `F`. -/
theorem isSymmetricAlgebra_symmetricAlgebra :
    SheafOfModules.GradedAlgebra.IsSymmetricAlgebra (symmetricAlgebra B S hS W F)
      (symmetricAlgebraGen B S hS W F) :=
  isSymmetricAlgebra_of_isoSource (symmetricAlgebraSheafificationIso B S hS W F)
    (@PresheafOfModules.isSymmetricAlgebra_symmetricAlgebraSheafify.{u, u + 1, u, u} _ _
      (SmallEtale.topology B S hS W.1) (structureSheaf B S hS W.1 W.2).obj
      (structureRingSheaf B S hS W) (𝟙 _) (isLocallyInjective_id_structureRingSheaf B S hS W)
      (isLocallySurjective_id_structureRingSheaf B S hS W)
      (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W) F.val)

/-- **Homogeneous multiplication in `Sym(F)` is commutative in every pair of integer degrees.**
This is what makes the relative spectrum of `Sym(F)` available with no further hypothesis. -/
theorem symmetricAlgebra_mul_comm (i j : ℤ) (V : (SmallEtale B S hS W.1)ᵒᵖ)
    (a : ((symmetricAlgebra B S hS W F).piece i).val.obj V)
    (b : ((symmetricAlgebra B S hS W F).piece j).val.obj V) :
    HEq (((symmetricAlgebra B S hS W F).mul i j).app V a b)
      (((symmetricAlgebra B S hS W F).mul j i).app V b a) :=
  @PresheafOfModules.symmetricAlgebraSheafify_mul_comm.{u, u + 1, u, u} _ _
    (SmallEtale.topology B S hS W.1) (structureSheaf B S hS W.1 W.2).obj
    (structureRingSheaf B S hS W) (𝟙 _) (isLocallyInjective_id_structureRingSheaf B S hS W)
    (isLocallySurjective_id_structureRingSheaf B S hS W)
    (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W) F.val
    i j V a b

/-- **`Sym(F)` as a sheaf of commutative `𝒪_W`-algebras**, the shape the relative spectrum
takes as input. -/
def symmetricAlgebraSheaf : AlgebraSheaf.{u, u} B S hS W.1 W.2 :=
  gradedAlgebraSheaf B S hS W (symmetricAlgebra B S hS W F)
    (symmetricAlgebra_mul_comm B S hS W F)

end SymmetricAlgebra

/-! ### The conormal sheaf and the two algebra sheaves -/

variable {X Z : AlgebraicSpaces B S hS}

/-- `𝒞_{Z/X,1}`, the degree-one piece of the conormal algebra of a morphism of algebraic spaces.
This is the conormal sheaf `𝒞_{Z/X}` of `i`, by the identification Stacks 09RQ itself makes; the
name records which description is taken, and keeps it apart from
`AlgebraicGeometry.Space.conormalSheaf`, the conormal sheaf of a formally unramified morphism
defined through its universal first order thickening. -/
abbrev conormalAlgebraPieceOne (i : Z ⟶ X) : SheafOfModules.{u} (structureRingSheaf B S hS Z) :=
  (conormalAlgebra B S hS i).piece 1

/-- **`𝒞_{Z/X,*}` as a sheaf of commutative `𝒪_Z`-algebras**: the ungraded realization of the
conormal algebra of Stacks 09RN. Commutativity of its homogeneous multiplication in every pair
of integer degrees is the hypothesis `hc`; see the implementation notes. -/
def conormalAlgebraSheaf (i : Z ⟶ X)
    (hc : ∀ (m n : ℤ) (V : (SmallEtale B S hS Z.1)ᵒᵖ)
      (a : ((conormalAlgebra B S hS i).piece m).val.obj V)
      (b : ((conormalAlgebra B S hS i).piece n).val.obj V),
      HEq (((conormalAlgebra B S hS i).mul m n).app V a b)
        (((conormalAlgebra B S hS i).mul n m).app V b a)) :
    AlgebraSheaf.{u, u} B S hS Z.1 Z.2 :=
  gradedAlgebraSheaf B S hS Z (conormalAlgebra B S hS i) hc

/-- `Sym(𝒞_{Z/X})` as a sheaf of commutative `𝒪_Z`-algebras, the algebra whose relative
spectrum is the normal bundle. -/
abbrev conormalSymmetricAlgebraSheaf (i : Z ⟶ X) : AlgebraSheaf.{u, u} B S hS Z.1 Z.2 :=
  symmetricAlgebraSheaf B S hS Z (conormalAlgebraPieceOne B S hS i)

end AlgebraicGeometry.Space

end
