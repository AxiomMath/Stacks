module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraDeterminant
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleLocalSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.InternalHomSheafAsSheafHom

/-!
# Stalkwise descent of invertibility for sheaves of modules of finite presentation

Let `(Y, 𝒪_Y)` be a ringed space and `M` a sheaf of `𝒪_Y`-modules of finite presentation whose
stalk `M_x` is an invertible `𝒪_{Y,x}`-module at every point. Then `M` is an invertible sheaf of
modules. This is the statement that
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorAlgebraDeterminant.lean` carries as the
`Prop` `Stacks.SheafOfModules.StalkwiseInvertibleDescent`, and it is discharged here by
`Stacks.SheafOfModules.stalkwiseInvertibleDescent`.

The proof is the third paragraph of the proof of
[Stacks, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K) read backwards. The dual sheaf
`M^∨ = SheafHom(M, 𝒪_Y)` and its evaluation pairing `M^∨ ⊗ M ⟶ 𝒪_Y` are global constructions;
at a point `x` the pairing becomes the contraction `Mᵛ_x ⊗ M_x → 𝒪_{Y,x}`, because for `M` of
finite presentation the stalk of `M^∨` is the dual of the stalk of `M` (Tag 01CP) and the
germs of a pointwise tensor product are the tensor product of the germs (Tag 01CB). Bijectivity
of that contraction *is* `Module.Invertible 𝒪_{Y,x} M_x`, so the pairing is locally bijective,
hence inverted by sheafification, and Tag 0B8K (2) ⟹ (1) turns a pairing that sheafification
inverts into invertibility.

**The finite presentation cannot be dropped**; the docstring of
`Stacks.SheafOfModules.StalkwiseInvertibleDescent` records the counterexample. This statement is
also not the stalkwise form of `Stacks.InvertibleLocallyFree.InvertibleIsLocal`, which descends
invertibility along a covering rather than along the stalks, and that theorem does not
discharge it: invertibility of a stalk is bijectivity of a contraction, not a trivialization, so
it yields no invertibility on any open and the covering `InvertibleIsLocal` consumes is never
produced.

## Main definitions

* `Stacks.SheafOfModules.StalkwiseDescent.dualM`: the dual sheaf `M^∨`, at the spellings of this
  file.
* `Stacks.SheafOfModules.StalkwiseDescent.evalPair`: the evaluation pairing `M^∨ ⊗ M ⟶ 𝒪_Y`.
* `Stacks.SheafOfModules.StalkwiseDescent.unitStalkEquiv`: the stalk of the structure sheaf
  regarded as a module over itself is free of rank one on the germ of the unit section.
* `Stacks.SheafOfModules.StalkwiseDescent.dualStalkEquiv`: **Tag 01CP for the dual sheaf** — for
  `M` of finite presentation the stalk of `M^∨` at `x` is the `𝒪_{Y,x}`-dual of `M_x`.

## Main results

* `Stacks.SheafOfModules.StalkwiseDescent.ringGerm_dualPair_sum`: **the germ of the evaluation
  pairing is the contraction of the stalks.** This is the compatibility of the two stalk
  comparisons with the evaluation morphism, and it is the one step of the argument that the
  repository did not have.
* `Stacks.SheafOfModules.StalkwiseDescent.exists_map_eq_zero_of_germ_tmul_sum_eq_zero`: Tag 01CB
  in the form the argument consumes — a relation between germs of a pointwise tensor product
  comes from a neighbourhood.
* `Stacks.SheafOfModules.StalkwiseDescent.exists_eval_eq_unitSec` and
  `Stacks.SheafOfModules.StalkwiseDescent.exists_map_eq_zero_of_eval_eq_zero`: the two halves of
  local bijectivity of the pairing, from surjectivity and injectivity of the contraction.
* `Stacks.SheafOfModules.StalkwiseDescent.isInvertible_of_stalk_invertible`: the theorem, for a
  fixed `M`.
* `Stacks.SheafOfModules.stalkwiseInvertibleDescent`: the `Prop`
  `Stacks.SheafOfModules.StalkwiseInvertibleDescent`, proved.

No Stacks attribute is attached. This is a step inside the proof of Tag 0B8K, not a clause of
it, and the tag of Tag 0FJN stays where it is until the hypotheses of
`Stacks.SheafOfModules.TensorExteriorSymmetricAlgebras.determinant_isInvertible_of_isFlat` come
off, which also needs the determinant hypothesis of that theorem.

## Implementation notes

**Two module structures on a stalk.** The repository carries two definitionally equal copies of
the `𝒪_{Y,x}`-module structure on the stalk of a sheaf of modules: Mathlib's, which
`Stacks.SheafOfModules.stalkModule` names and which Tag 01CP is stated over, and the one built
for Tag 01CB in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorStalkRingedSpace.lean`. They are *not*
definitionally equal — the second is defined by choosing germ representatives — and
`Stacks.SheafOfModules.stalkModule_eq` is what passes between them. Everything below is stated
over Mathlib's; the single place where Tag 01CB is used,
`exists_map_eq_zero_of_germ_tmul_sum_eq_zero`, takes the two module structures as explicit
arguments together with equations identifying them with Tag 01CB's, so that the transport is one
`subst` and no statement elsewhere has to mention the other copy.

**Why `evalPair` exists.** `Stacks.SheafOfModules.evaluationPresheaf` has its source and target
spelled through `TensorSheafification.structureSheaf Y.presheaf`, whereas `M.val` is indexed by
`(Oring Y).obj`. The two sheaves of rings are the same, but instance search does not cross
between the spellings — unifying them needs `CategoryTheory.sheafCompose` unfolded — so the
module structures on the sections are found at one spelling and not at the other. `evalPair` is
that morphism with its type ascribed at the spelling `M.val` carries; `evalPair_eq` is `rfl`.
For the same reason `moduleSectionCommRingCat` and `monoidalPresheafModules` are declared by
hand as local instances.

## References

* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TensorProduct
open AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules.StalkwiseDescent

open SheafHomStalk (sheafHomStalkLinearEquivOfFinitePresentation)

/-- The structure sheaf of a ringed space, read as a sheaf of (not necessarily commutative)
rings. This is `structureSheafRing`, abbreviated because the bare name is
ambiguous inside this namespace. -/
noncomputable abbrev Oring (Y : RingedSpace.{u, u}) :
    Sheaf (Opens.grothendieckTopology (Y.carrier : Type u)) RingCat.{u} :=
  structureSheafRing Y

variable {Y : RingedSpace.{u, u}}

/-- The stalk of the structure sheaf of a ringed space at a point, as a type. -/
abbrev ringStalkType (Y : RingedSpace.{u, u}) (x : Y) : Type u := ToType (Y.presheaf.stalk x)

/-- The stalk of a sheaf of modules at a point, as a type. -/
abbrev stalkType (F : _root_.SheafOfModules.{u} (Oring Y)) (x : Y) : Type u :=
  ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) F.val.presheaf x)

/-- The structure sheaf viewed as a module over itself. -/
noncomputable abbrev unitMod (Y : RingedSpace.{u, u}) : _root_.SheafOfModules.{u} (Oring Y) :=
  _root_.SheafOfModules.unit (Oring Y)

/-- The unit section `1 ∈ 𝒪_Y(U)`, read as a section of the structure sheaf regarded as a
module over itself. -/
noncomputable def unitSec (Y : RingedSpace.{u, u}) (U : Opens Y) :
    ToType ((unitMod Y).val.obj (op U)) :=
  (1 : ToType ((Oring Y).obj.obj (op U)))

/-- The germ at `x` of the unit section. -/
noncomputable def unitGerm (x : Y) : stalkType (unitMod Y) x :=
  germ (unitMod Y) x (U := ⊤) trivial (unitSec Y ⊤)

/-- The germ of the unit section over any neighbourhood of `x` is `unitGerm x`. -/
lemma germ_unitSec (x : Y) (U : Opens Y) (hx : x ∈ U) :
    germ (unitMod Y) x hx (unitSec Y U) = unitGerm x := by
  have h : res (unitMod Y) (homOfLE (le_top (a := U))) (unitSec Y ⊤) = unitSec Y U :=
    map_one ((Oring Y).obj.map (homOfLE (le_top (a := U))).op).hom
  rw [unitGerm, ← h, germ_res]

/-- The germ of a section of the structure sheaf, read in the stalk of the structure sheaf as a
module over itself, is its ring germ acting on the germ of the unit section. -/
lemma ringGerm_smul_unitGerm (x : Y) {U : Opens Y} (hx : x ∈ U)
    (a : ToType ((Oring Y).obj.obj (op U))) :
    letI := stalkModule (unitMod Y) x
    ringGerm x hx a • unitGerm x = germ (unitMod Y) x hx a := by
  let := stalkModule (unitMod Y) x
  rw [← germ_unitSec x U hx, ← germ_commRingCat_smul (unitMod Y) x hx a (unitSec Y U)]
  exact congrArg (germ (unitMod Y) x hx) (mul_one (show Y.presheaf.obj (op U) from a))

/-- **The stalk of the structure sheaf, regarded as a module over itself, is free of rank one
on the germ of the unit section.** This identifies the target of the Tag 01CP stalk comparison
for the dual sheaf with the local ring itself. -/
noncomputable def unitStalkEquiv (x : Y) :
    letI := stalkModule (unitMod Y) x
    ringStalkType Y x ≃ₗ[ringStalkType Y x] stalkType (unitMod Y) x := by
  let := stalkModule (unitMod Y) x
  refine LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (ringStalkType Y x) (stalkType (unitMod Y) x) (unitGerm x)) ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr ?_
    intro a ha
    obtain ⟨U, hxU, s, rfl⟩ := exists_ringGerm_eq x a
    rw [LinearMap.toSpanSingleton_apply, ringGerm_smul_unitGerm x hxU s] at ha
    obtain ⟨W, h, hxW, hres⟩ := exists_res_eq (M := unitMod Y) x hxU s 0
      (ha.trans (germ_zero x hxU).symm)
    have h0 : res (unitMod Y) h (0 : ToType ((unitMod Y).val.obj (op U))) = 0 :=
      map_zero ((unitMod Y).val.map h.op).hom
    rw [← ringGerm_resR x h hxW s, show resR (Oring Y) h s = res (unitMod Y) h s from rfl, hres,
      h0]
    exact map_zero (Y.presheaf.germ W x hxW).hom
  · intro m
    obtain ⟨U, hxU, s, rfl⟩ := exists_germ_eq (unitMod Y) x m
    exact ⟨ringGerm x hxU s, (LinearMap.toSpanSingleton_apply ..).trans
      (ringGerm_smul_unitGerm x hxU s)⟩

/-- The identification of the local ring with the stalk of the structure sheaf as a module over
itself is multiplication on the germ of the unit section. -/
lemma unitStalkEquiv_apply (x : Y) (a : ringStalkType Y x) :
    letI := stalkModule (unitMod Y) x
    unitStalkEquiv x a = a • unitGerm x := rfl

/-- On the germ of a section, the identification is the ring germ. -/
lemma unitStalkEquiv_germ (x : Y) {U : Opens Y} (hx : x ∈ U)
    (a : ToType ((Oring Y).obj.obj (op U))) :
    unitStalkEquiv x (ringGerm x hx a) = germ (unitMod Y) x hx a :=
  ringGerm_smul_unitGerm x hx a

/-- The inverse identification sends the germ of a section to its ring germ. -/
lemma unitStalkEquiv_symm_germ (x : Y) {U : Opens Y} (hx : x ∈ U)
    (a : ToType ((Oring Y).obj.obj (op U))) :
    (unitStalkEquiv x).symm (germ (unitMod Y) x hx a) = ringGerm x hx a := by
  rw [LinearEquiv.symm_apply_eq, unitStalkEquiv_germ]

/-- The module structure of the sections of a sheaf of `𝒪_Y`-modules over the
`CommRingCat`-valued sections of the structure sheaf. Instance search does not find it: unifying
the base sheaf of rings of `F.val` with a composite `· ⋙ forget₂ CommRingCat RingCat` requires
unfolding `CategoryTheory.sheafCompose`. -/
local instance moduleSectionCommRingCat (F : _root_.SheafOfModules.{u} (Oring Y))
    (U : (Opens Y)ᵒᵖ) : Module (ToType (Y.presheaf.obj U)) (ToType (F.val.obj U)) :=
  inferInstanceAs (Module (ToType ((Oring Y).obj.obj U)) (ToType (F.val.obj U)))

/-! ### The dual sheaf and Tag 01CP -/

variable (M : _root_.SheafOfModules.{u} (Oring Y))

/-- The sheaf condition for the structure sheaf of `Y`, in the form in which the
tensor-sheafification development takes it. -/
abbrev hRing (Y : RingedSpace.{u, u}) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology (Y.carrier : Type u))
      (TensorSheafification.structureRingPresheaf Y.presheaf) :=
  CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf _ Y.presheaf
    (forget₂ CommRingCat.{u} RingCat.{u}) Y.IsSheaf

/-- The monoidal structure on presheaves of `𝒪_Y`-modules, at the spelling of the index that
`M.val` carries. Instance search does not find
`Stacks.SheafOfModules.monoidalCategoryPresheafOfModules` there, because that one is stated for
the index spelled `(TensorSheafification.structureSheaf 𝒪 h𝒪).obj`. -/
noncomputable local instance monoidalPresheafModules (Y : RingedSpace.{u, u}) :
    MonoidalCategory (PresheafOfModules.{u} (Oring Y).obj) :=
  monoidalCategoryPresheafOfModules Y.presheaf (hRing Y)

/-- The dual sheaf `M^∨ = SheafHom(M, 𝒪_Y)`. -/
noncomputable abbrev dualM : _root_.SheafOfModules.{u} (Oring Y) :=
  dualSheaf Y.presheaf (hRing Y) M

/-- `M^∨` read as a term of the structure `SheafHom` of Tag 01CO, which is what the stalk
comparison of Tag 01CP consumes. -/
noncomputable abbrev shHom : SheafHom Y.sheaf M (unitMod Y) :=
  internalHomSheafHom Y.sheaf M (unitMod Y)

/-- The value of a section of `M^∨` over `U` on a section of `M` over `U`. -/
noncomputable def dualPair {U : Opens Y} (α : (dualM M).val.obj (op U))
    (m : M.val.obj (op U)) : (Oring Y).obj.obj (op U) :=
  α.app (op (Over.mk (𝟙 U))) m

/-- **Tag 01CP for the dual sheaf.** For `M` of finite presentation the canonical map from the
stalk of `M^∨` at `x` to the module of `𝒪_{Y,x}`-linear maps from `M_x` to the stalk of the
structure sheaf as a module over itself is an isomorphism. -/
noncomputable def sheafHomStalk (hfp : M.IsFinitePresentation) (x : Y) :
    letI := stalkModule M x
    letI := stalkModule (dualM M) x
    letI := stalkModule (unitMod Y) x
    stalkType (dualM M) x ≃ₗ[ringStalkType Y x]
      (stalkType M x →ₗ[ringStalkType Y x] stalkType (unitMod Y) x) :=
  let := stalkModule M x
  let := stalkModule (dualM M) x
  let := stalkModule (unitMod Y) x
  have : (show _root_.SheafOfModules.{u} (_root_.structureSheaf Y.sheaf) from
    M).IsFinitePresentation := hfp
  show stalkType (dualM M) x ≃ₗ[ringStalkType Y x]
      (stalkType M x →ₗ[ringStalkType Y x] stalkType (unitMod Y) x) from
    (sheafHomStalkLinearEquivOfFinitePresentation (shHom M) x).equiv

/-- The Tag 01CP comparison on germs: it sends the germ of a local section of `M^∨`, evaluated
at the germ of a local section of `M`, to the germ of the value. -/
lemma sheafHomStalk_germ (hfp : M.IsFinitePresentation) (x : Y) {U : Opens Y} (hx : x ∈ U)
    (α : (dualM M).val.obj (op U)) (m : M.val.obj (op U)) :
    sheafHomStalk M hfp x (germ (dualM M) x hx α) (germ M x hx m)
      = germ (unitMod Y) x hx (dualPair M α m) := by
  let := stalkModule M x
  let := stalkModule (dualM M) x
  let := stalkModule (unitMod Y) x
  have : (show _root_.SheafOfModules.{u} (_root_.structureSheaf Y.sheaf) from
    M).IsFinitePresentation := hfp
  exact (sheafHomStalkLinearEquivOfFinitePresentation (shHom M) x).germ_apply U hx α m

/-- **Tag 01CP for the dual sheaf**, with the target read as the `𝒪_{Y,x}`-dual of `M_x`
through the identification of the stalk of the structure sheaf as a module over itself with the
local ring. -/
noncomputable def dualStalkEquiv (hfp : M.IsFinitePresentation) (x : Y) :
    letI := stalkModule M x
    letI := stalkModule (dualM M) x
    stalkType (dualM M) x ≃ₗ[ringStalkType Y x]
      Module.Dual (ringStalkType Y x) (stalkType M x) :=
  let := stalkModule M x
  let := stalkModule (dualM M) x
  let := stalkModule (unitMod Y) x
  (sheafHomStalk M hfp x).trans (unitStalkEquiv x).symm.congrRight

/-- **The compatibility of the Tag 01CP comparison with the evaluation pairing on germs.** The
dual of the stalk that `dualStalkEquiv` produces sends the germ of a local section of `M^∨`,
evaluated at the germ of a local section of `M`, to the germ of the value. -/
lemma dualStalkEquiv_germ (hfp : M.IsFinitePresentation) (x : Y) {U : Opens Y} (hx : x ∈ U)
    (α : (dualM M).val.obj (op U)) (m : M.val.obj (op U)) :
    dualStalkEquiv M hfp x (germ (dualM M) x hx α) (germ M x hx m)
      = ringGerm x hx (dualPair M α m) := by
  let := stalkModule M x
  let := stalkModule (dualM M) x
  let := stalkModule (unitMod Y) x
  change (unitStalkEquiv x).symm
      (sheafHomStalk M hfp x (germ (dualM M) x hx α) (germ M x hx m)) = _
  rw [sheafHomStalk_germ M hfp x hx α m]
  exact unitStalkEquiv_symm_germ x hx _

/-! ### Tag 01CB in the form the injectivity step needs -/

open TensorStalkRingedSpace in
/-- **A relation between germs of a pointwise tensor product comes from a neighbourhood.** If a
finite sum of pure tensors of germs vanishes in `A_x ⊗_{𝒪_{Y,x}} B_x`, then the corresponding
section of the pointwise tensor product `A ⊗ B` restricts to zero on a neighbourhood of `x`.

This is the injectivity half of Tag 01CB,
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso`, taken at the *pointwise* tensor
product, where no sheafification intervenes. The two module structures `iA`, `iB` on the stalks
are arguments rather than instances: the repository carries two definitionally equal copies of
each, Tag 01CB is stated for the one built there and Tag 01CP for Mathlib's, and
`Stacks.SheafOfModules.stalkModule_eq` is what passes between them. -/
lemma exists_map_eq_zero_of_germ_tmul_sum_eq_zero
    (A B : _root_.SheafOfModules.{u} (Oring Y)) (x : Y) {U : Opens Y} (hx : x ∈ U)
    {ι : Type*} (t : Finset ι) (a : ι → A.val.obj (op U)) (b : ι → B.val.obj (op U))
    (iA : Module (ringStalkType Y x) (stalkType A x))
    (iB : Module (ringStalkType Y x) (stalkType B x))
    (hiA : iA = TensorStalkRingedSpace.stalkModule Y A.val x)
    (hiB : iB = TensorStalkRingedSpace.stalkModule Y B.val x)
    (h : ∑ i ∈ t, @TensorProduct.tmul (ringStalkType Y x) _ (stalkType A x) (stalkType B x) _ _
          iA iB (germ A x hx (a i)) (germ B x hx (b i)) = 0) :
    ∃ (V : Opens Y) (f : V ⟶ U), x ∈ V ∧
      ((PresheafOfModules.tensorObj (O := Y.presheaf) A.val B.val).map f.op).hom
        (∑ i ∈ t, a i ⊗ₜ[Y.presheaf.obj (op U)] b i) = 0 := by
  subst hiA
  subst hiB
  obtain ⟨Φ, hΦ⟩ := exists_presheafTensorStalkIso Y x A B
  set g : (PresheafOfModules.tensorObj (O := Y.presheaf) A.val B.val).obj (op U) →+
      grpStalk Y (PresheafOfModules.tensorObj (O := Y.presheaf) A.val B.val) x :=
    grpGerm Y (PresheafOfModules.tensorObj (O := Y.presheaf) A.val B.val) x U hx with hg
  set s0 : (PresheafOfModules.tensorObj (O := Y.presheaf) A.val B.val).obj (op U) :=
    ∑ i ∈ t, a i ⊗ₜ[Y.presheaf.obj (op U)] b i with hs0
  have hz : g s0 = 0 := by
    refine Φ.injective (Eq.trans ?_ (map_zero Φ).symm)
    calc Φ (g s0)
        = Φ (∑ i ∈ t, g (a i ⊗ₜ[Y.presheaf.obj (op U)] b i)) :=
          congrArg Φ (Eq.trans (congrArg g hs0) (map_sum g _ t))
      _ = ∑ i ∈ t, Φ (g (a i ⊗ₜ[Y.presheaf.obj (op U)] b i)) := map_sum Φ.toLinearMap _ t
      _ = 0 := Eq.trans (Finset.sum_congr rfl fun i _ => hΦ U hx (a i) (b i)) h
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq (C := AddCommGrpCat.{u})
    (PresheafOfModules.tensorObj (O := Y.presheaf) A.val B.val).presheaf x hx hx s0 0
      (hz.trans (map_zero _).symm)
  refine ⟨W, iU, hxW, hs0 ▸ hW.trans ?_⟩
  exact map_zero
    ((PresheafOfModules.tensorObj (O := Y.presheaf) A.val B.val).presheaf.map iV.op).hom

/-! ### The stalk of the evaluation pairing is the contraction -/

/-- The pointwise tensor product `M^∨ ⊗ M`, the source of the evaluation pairing. Spelled
through `CategoryTheory.MonoidalCategory.tensorObj` because the `⊗` notation of the monoidal
category and the `⊗` of `TensorProduct` are both in scope here. -/
noncomputable abbrev dualTensor : PresheafOfModules.{u} (Oring Y).obj :=
  MonoidalCategory.tensorObj (dualM M).val M.val

/-- The evaluation pairing `M^∨ ⊗ M ⟶ 𝒪_Y` of
`Stacks.SheafOfModules.evaluationPresheaf`, with its source and target spelled through
`Oring Y` rather than through `TensorSheafification.structureSheaf`. The two spellings of the
sheaf of rings are the same, but only one of them lets instance search find the module
structures on the sections. -/
noncomputable def evalPair : dualTensor M ⟶ (unitMod Y).val :=
  show dualTensor M ⟶ (unitMod Y).val from evaluationPresheaf Y.presheaf (hRing Y) M

/-- `evalPair` is `Stacks.SheafOfModules.evaluationPresheaf`; only the spelling of its source
and target differs. -/
lemma evalPair_eq : evalPair M = evaluationPresheaf Y.presheaf (hRing Y) M := rfl

/-- The evaluation pairing `M^∨ ⊗ M ⟶ 𝒪_Y` sends a pure tensor of sections to the value of the
first on the second. -/
lemma evaluationPresheaf_tmul_dualPair {U : Opens Y} (α : (dualM M).val.obj (op U))
    (m : M.val.obj (op U)) :
    ((evalPair M).app (op U)).hom
        (α ⊗ₜ[Y.presheaf.obj (op U)] m) = dualPair M α m := rfl

/-- The evaluation pairing on a finite sum of pure tensors of sections. -/
lemma evaluationPresheaf_sum {U : Opens Y} {ι : Type*} (t : Finset ι)
    (α : ι → (dualM M).val.obj (op U)) (m : ι → M.val.obj (op U)) :
    ((evalPair M).app (op U)).hom
        (∑ i ∈ t, α i ⊗ₜ[Y.presheaf.obj (op U)] m i)
      = ∑ i ∈ t, dualPair M (α i) (m i) := by
  refine Eq.trans (map_sum ((evalPair M).app (op U)).hom _ t) ?_
  exact Finset.sum_congr rfl fun i _ => evaluationPresheaf_tmul_dualPair M (α i) (m i)

/-- **The germ at `x` of the evaluation pairing is the contraction of the stalks.** This is the
compatibility of the two stalk comparisons — Tag 01CP for `M^∨` and Tag 01CB for the tensor
product — with the evaluation morphism: on a finite sum of pure tensors of local sections, the
germ of the value of the pairing is the contraction `Mᵛ_x ⊗ M_x → 𝒪_{Y,x}` applied to the
corresponding sum of germs. -/
lemma ringGerm_dualPair_sum (hfp : M.IsFinitePresentation) (x : Y) {U : Opens Y} (hx : x ∈ U)
    {ι : Type*} (t : Finset ι)
    (α : ι → (dualM M).val.obj (op U)) (m : ι → M.val.obj (op U)) :
    letI := stalkModule M x
    letI := stalkModule (dualM M) x
    ringGerm x hx (∑ i ∈ t, dualPair M (α i) (m i))
      = contractLeft (ringStalkType Y x) (stalkType M x)
          (∑ i ∈ t, (dualStalkEquiv M hfp x (germ (dualM M) x hx (α i))) ⊗ₜ
            (germ M x hx (m i))) := by
  let := stalkModule M x
  let := stalkModule (dualM M) x
  refine Eq.trans (ringGerm_sum x hx t _) ?_
  refine Eq.symm (Eq.trans (map_sum (contractLeft (ringStalkType Y x) (stalkType M x)) _ t) ?_)
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Eq.trans (contractLeft_apply _ _) (dualStalkEquiv_germ M hfp x hx (α i) (m i))

/-! ### Local bijectivity of the evaluation pairing -/

/-- **A section of `M^∨ ⊗ M` killed by the evaluation pairing dies on a neighbourhood of any
point.** The germ of the section at `x` corresponds, by Tag 01CB and Tag 01CP, to an element of
`Mᵛ_x ⊗ M_x` which the contraction kills; the contraction is injective because `M_x` is
invertible, so that element is zero, and a relation between germs of a pointwise tensor product
comes from a neighbourhood. -/
lemma exists_map_eq_zero_of_eval_eq_zero (hfp : M.IsFinitePresentation)
    (hinv : ∀ x : Y, letI := stalkModule M x
      Module.Invertible (ringStalkType Y x) (stalkType M x))
    (p : Y) {U : Opens Y} (hp : p ∈ U) (v : (dualTensor M).obj (op U))
    (hv : ((evalPair M).app (op U)).hom v = 0) :
    ∃ (V : Opens Y) (f : V ⟶ U), p ∈ V ∧ ((dualTensor M).map f.op).hom v = 0 := by
  let := stalkModule M p
  let := stalkModule (dualM M) p
  have := hinv p
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset
    (show TensorProduct (ToType (Y.presheaf.obj (op U))) (ToType ((dualM M).val.obj (op U)))
      (ToType (M.val.obj (op U))) from v)
  have hsum : ∑ i ∈ S, dualPair M i.1 i.2 = 0 :=
    (evaluationPresheaf_sum M S (fun i => i.1) (fun i => i.2)).symm.trans
      ((congrArg (fun z => ((evalPair M).app (op U)).hom z)
        hS).symm.trans hv)
  have hcontract : contractLeft (ringStalkType Y p) (stalkType M p)
      (∑ i ∈ S, (dualStalkEquiv M hfp p (germ (dualM M) p hp i.1)) ⊗ₜ (germ M p hp i.2)) = 0 := by
    refine (ringGerm_dualPair_sum M hfp p hp S (fun i => i.1) (fun i => i.2)).symm.trans ?_
    rw [hsum]
    exact map_zero (Y.presheaf.germ U p hp).hom
  have h0 : ∑ i ∈ S, (dualStalkEquiv M hfp p (germ (dualM M) p hp i.1)) ⊗ₜ[ringStalkType Y p]
      (germ M p hp i.2) = 0 :=
    Module.Invertible.bijective.injective (hcontract.trans (map_zero _).symm)
  have hT : ∑ i ∈ S, (germ (dualM M) p hp i.1) ⊗ₜ[ringStalkType Y p]
      (germ M p hp i.2) = 0 := by
    refine ((dualStalkEquiv M hfp p).rTensor (stalkType M p)).injective ?_
    refine Eq.trans (map_sum ((dualStalkEquiv M hfp p).rTensor (stalkType M p)) _ S) ?_
    exact Eq.trans (Finset.sum_congr rfl fun i _ => LinearEquiv.rTensor_tmul ..)
      (h0.trans (map_zero _).symm)
  obtain ⟨V, f, hpV, hzero⟩ := exists_map_eq_zero_of_germ_tmul_sum_eq_zero (dualM M) M p hp S
    (fun i => i.1) (fun i => i.2) _ _ (stalkModule_eq Y (dualM M).val p).symm
    (stalkModule_eq Y M.val p).symm hT
  refine ⟨V, f, hpV, ?_⟩
  rw [hS]
  exact hzero

/-- **The evaluation pairing hits the unit section near every point.** Invertibility of `M_x`
makes the contraction `Mᵛ_x ⊗ M_x → 𝒪_{Y,x}` surjective, so `1` is a finite sum of contractions
of germs; Tag 01CP realises each dual germ by a local section of `M^∨`, and the resulting sum of
pure tensors pairs to a section whose germ is `1`, hence to `1` after shrinking. -/
lemma exists_eval_eq_unitSec (hfp : M.IsFinitePresentation)
    (hinv : ∀ x : Y, letI := stalkModule M x
      Module.Invertible (ringStalkType Y x) (stalkType M x))
    (p : Y) {U : Opens Y} (hp : p ∈ U) :
    ∃ (V : Opens Y) (_ : V ⟶ U) (_ : p ∈ V) (t : (dualTensor M).obj (op V)),
      ((evalPair M).app (op V)).hom t = unitSec Y V := by
  classical
  let := stalkModule M p
  let := stalkModule (dualM M) p
  let := stalkModule (unitMod Y) p
  have := hinv p
  obtain ⟨z, hz⟩ := (Module.Invertible.bijective (R := ringStalkType Y p)
    (M := stalkType M p)).surjective (1 : ringStalkType Y p)
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset z
  choose Ua hpa aa ha using fun q : Module.Dual (ringStalkType Y p) (stalkType M p) ×
    stalkType M p => exists_germ_eq (dualM M) p ((dualStalkEquiv M hfp p).symm q.1)
  choose Ub hpb bb hb using fun q : Module.Dual (ringStalkType Y p) (stalkType M p) ×
    stalkType M p => exists_germ_eq M p q.2
  obtain ⟨V₀, f₀, hpV₀, hle⟩ := exists_nbhd_le' p U hp
    (fun i : {q // q ∈ S} => Ua i.1 ⊓ Ub i.1) (fun i => ⟨hpa i.1, hpb i.1⟩)
  set A : {q // q ∈ S} → (dualM M).val.obj (op V₀) := fun i =>
    res (dualM M) (homOfLE (le_trans (hle i) inf_le_left)) (aa i.1) with hA
  set B : {q // q ∈ S} → M.val.obj (op V₀) := fun i =>
    res M (homOfLE (le_trans (hle i) inf_le_right)) (bb i.1) with hB
  have hgA : ∀ i, dualStalkEquiv M hfp p (germ (dualM M) p hpV₀ (A i)) = i.1.1 := fun i => by
    rw [hA]
    rw [germ_res p (homOfLE (le_trans (hle i) inf_le_left)) hpV₀ (aa i.1), ha i.1,
      LinearEquiv.apply_symm_apply]
  have hgB : ∀ i, germ M p hpV₀ (B i) = i.1.2 := fun i => by
    rw [hB, germ_res p (homOfLE (le_trans (hle i) inf_le_right)) hpV₀ (bb i.1), hb i.1]
  have hone : ringGerm p hpV₀ (∑ i ∈ S.attach, dualPair M (A i) (B i))
      = ringGerm p hpV₀ (unitSec Y V₀) := by
    rw [ringGerm_dualPair_sum M hfp p hpV₀ S.attach A B]
    have hsum : ∑ i ∈ S.attach, (dualStalkEquiv M hfp p (germ (dualM M) p hpV₀ (A i)))
        ⊗ₜ[ringStalkType Y p] (germ M p hpV₀ (B i)) = z :=
      calc ∑ i ∈ S.attach, (dualStalkEquiv M hfp p (germ (dualM M) p hpV₀ (A i)))
              ⊗ₜ[ringStalkType Y p] (germ M p hpV₀ (B i))
          = ∑ i ∈ S.attach, i.1.1 ⊗ₜ[ringStalkType Y p] i.1.2 :=
            Finset.sum_congr rfl fun i _ => by rw [hgA i, hgB i]
        _ = ∑ q ∈ S, q.1 ⊗ₜ[ringStalkType Y p] q.2 :=
            Finset.sum_attach S (fun q => q.1 ⊗ₜ[ringStalkType Y p] q.2)
        _ = z := hS.symm
    rw [hsum, hz]
    exact (map_one (Y.presheaf.germ V₀ p hpV₀).hom).symm
  have hgerm : germ (unitMod Y) p hpV₀ (∑ i ∈ S.attach, dualPair M (A i) (B i))
      = germ (unitMod Y) p hpV₀ (unitSec Y V₀) :=
    (unitStalkEquiv_germ p hpV₀ (∑ i ∈ S.attach, dualPair M (A i) (B i))).symm.trans
      ((congrArg (fun r => unitStalkEquiv p r) hone).trans
        (unitStalkEquiv_germ p hpV₀ (unitSec Y V₀)))
  obtain ⟨W, g, hpW, hres⟩ := exists_res_eq (M := unitMod Y) p hpV₀
    (∑ i ∈ S.attach, dualPair M (A i) (B i)) (unitSec Y V₀) hgerm
  refine ⟨W, g ≫ f₀, hpW, ((dualTensor M).map g.op).hom
    (∑ i ∈ S.attach, A i ⊗ₜ[Y.presheaf.obj (op V₀)] B i), ?_⟩
  refine Eq.trans (PresheafOfModules.naturality_apply (evalPair M) g.op _) ?_
  refine Eq.trans (congrArg (fun w => res (unitMod Y) g w)
    (evaluationPresheaf_sum M S.attach A B)) ?_
  refine Eq.trans hres ?_
  exact map_one ((Oring Y).obj.map g.op).hom

/-- **The evaluation pairing of `M` with its dual is locally surjective.** -/
theorem isLocallySurjective_evaluationPresheaf (hfp : M.IsFinitePresentation)
    (hinv : ∀ x : Y, letI := stalkModule M x
      Module.Invertible (ringStalkType Y x) (stalkType M x)) :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology (Y.carrier : Type u))
      ((PresheafOfModules.toPresheaf (Oring Y).obj).map (evalPair M)) := by
  constructor
  intro U r p hp
  obtain ⟨V, f, hpV, t, ht⟩ := exists_eval_eq_unitSec M hfp hinv p (U := U) hp
  have key : ((evalPair M).app (op V)).hom
      ((resR (Oring Y) f r) • t) = resR (Oring Y) f r := by
    refine Eq.trans (((evalPair M).app (op V)).hom.map_smul
      (resR (Oring Y) f r) t) ?_
    refine Eq.trans (congrArg (fun w => (resR (Oring Y) f r) • w) ht) ?_
    exact mul_one (show Y.presheaf.obj (op V) from resR (Oring Y) f r)
  exact ⟨V, f, ⟨(resR (Oring Y) f r) • t, key⟩, hpV⟩

/-- **The evaluation pairing of `M` with its dual is locally injective.** -/
theorem isLocallyInjective_evaluationPresheaf (hfp : M.IsFinitePresentation)
    (hinv : ∀ x : Y, letI := stalkModule M x
      Module.Invertible (ringStalkType Y x) (stalkType M x)) :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology (Y.carrier : Type u))
      ((PresheafOfModules.toPresheaf (Oring Y).obj).map (evalPair M)) := by
  constructor
  intro Z w w' hww p hp
  have hv : ((evalPair M).app (op Z.unop)).hom
      ((w : ToType ((dualTensor M).obj (op Z.unop))) -
        (w' : ToType ((dualTensor M).obj (op Z.unop)))) = 0 :=
    (map_sub ((evalPair M).app (op Z.unop)).hom _ _).trans (sub_eq_zero.mpr hww)
  obtain ⟨V, f, hpV, h0⟩ :=
    exists_map_eq_zero_of_eval_eq_zero M hfp hinv p (U := Z.unop) hp _ hv
  refine ⟨V, f, ?_, hpV⟩
  have h1 : ((dualTensor M).map f.op).hom (w : ToType ((dualTensor M).obj (op Z.unop)))
      - ((dualTensor M).map f.op).hom (w' : ToType ((dualTensor M).obj (op Z.unop))) = 0 :=
    (map_sub ((dualTensor M).map f.op).hom _ _).symm.trans h0
  exact sub_eq_zero.mp h1

/-- **Sheafification inverts the evaluation pairing of `M` with its dual.** -/
theorem isIso_sheafify_map_evaluationPresheaf (hfp : M.IsFinitePresentation)
    (hinv : ∀ x : Y, letI := stalkModule M x
      Module.Invertible (ringStalkType Y x) (stalkType M x)) :
    letI : HasSheafify (Opens.grothendieckTopology (Y.carrier : Type u)) AddCommGrpCat.{u} :=
      hasSheafify_opens
    letI : (Opens.grothendieckTopology (Y.carrier : Type u)).WEqualsLocallyBijective
        AddCommGrpCat.{u} := wEqualsLocallyBijective_opens
    IsIso ((TensorSheafification.sheafify Y.presheaf (hRing Y)).map
      (evaluationPresheaf Y.presheaf (hRing Y) M)) :=
  let : HasSheafify (Opens.grothendieckTopology (Y.carrier : Type u)) AddCommGrpCat.{u} :=
    hasSheafify_opens
  let : (Opens.grothendieckTopology (Y.carrier : Type u)).WEqualsLocallyBijective
      AddCommGrpCat.{u} := wEqualsLocallyBijective_opens
  isIso_sheafify_map_of_isLocallyBijective Y.presheaf (hRing Y)
    (evaluationPresheaf Y.presheaf (hRing Y) M)
    (isLocallyInjective_evaluationPresheaf M hfp hinv)
    (isLocallySurjective_evaluationPresheaf M hfp hinv)

attribute [local instance] symmetricCategoryPresheafOfModules

/-- **A sheaf of modules of finite presentation on a ringed space all of whose stalks are
invertible modules is invertible.** -/
theorem isInvertible_of_stalk_invertible (hfp : M.IsFinitePresentation)
    (hinv : ∀ x : Y, letI := stalkModule M x
      Module.Invertible (ringStalkType Y x) (stalkType M x)) :
    AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf (hRing Y) M := by
  have hev := isIso_sheafify_map_evaluationPresheaf M hfp hinv
  exact isInvertible_of_pairing (O := Y.presheaf) (hO := hRing Y) M (dualM M)
    (evaluationPresheaf Y.presheaf (hRing Y) M)
    ((braidingVal Y.presheaf (hRing Y) M (dualM M)).inv ≫
      evaluationPresheaf Y.presheaf (hRing Y) M) hev
    (isIso_sheafify_map_comp Y.presheaf (hRing Y) _ _ inferInstance hev)

end Stacks.SheafOfModules.StalkwiseDescent

namespace Stacks.SheafOfModules

/-- **Stalkwise descent of invertibility for sheaves of modules of finite presentation.** A
sheaf of modules of finite presentation on a ringed space whose every stalk is an invertible
module is an invertible sheaf of modules.

This discharges `Stacks.SheafOfModules.StalkwiseInvertibleDescent`, which the determinant
development carries as a hypothesis. -/
theorem stalkwiseInvertibleDescent (Y : AlgebraicGeometry.RingedSpace.{u, u}) :
    StalkwiseInvertibleDescent Y := fun M hfp hinv =>
  StalkwiseDescent.isInvertible_of_stalk_invertible M hfp hinv

end Stacks.SheafOfModules

end
