module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatExtendScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inverse image of a tensor product of sheaves of modules, as an isomorphism

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi. The inverse image of
sheaves of modules of **Stacks 03D2** — the first of the two factors of the pullback of
Stacks 03D6, part (2) — carries a tensor product of sheaves of `O_D`-modules to the tensor
product, over `f⁻¹O_D`, of the inverse images:

`f⁻¹(F ⊗_{O_D} G) ≅ f⁻¹F ⊗_{f⁻¹O_D} f⁻¹G`,

naturally in `F` and in `G`. This is the comparison of Stacks 03EL with the extension of scalars
along `f♯` left off; the comparison for extension of scalars is
`Stacks.Sheaves.RingedToposModules.extendScalarsTensorIso` (Stacks 03CU).

The proof is the first four links of the chain of
`Stacks.SheafOfModules.pullbackTensorHomEquiv`, read at an arbitrary sheaf of `f⁻¹O_D`-modules
`M` as the sheaf of values instead of at one of the form `N|_{f⁻¹O_D}`:

1. `Hom_{f⁻¹O_D}(f⁻¹(F ⊗ G), M) = Hom_{O_D}(F ⊗ G, f_*M)` — the adjunction of Stacks 03D4;
2. `Hom_{O_D}(F ⊗ G, f_*M) = Bilin_{O_D}(F × G, f_*M)` — the universal property of the tensor
   product sheaf;
3. `Bilin_{O_D}(F × G, f_*M) = Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, M)` — the step the source of
   Stacks 03EL calls the interesting one;
4. `Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, M) = Hom_{f⁻¹O_D}(f⁻¹F ⊗_{f⁻¹O_D} f⁻¹G, M)` — the universal
   property again, over `f⁻¹O_D`.

Each link is natural in `M` and in the pair `(F, G)`, so `CategoryTheory.Functor.natIsoOfHomEquiv`
turns the composite into an isomorphism of bifunctors.

## Main definitions

* `Stacks.SheafOfModules.inverseImageTensorBifunctor`: the tensor product of sheaves of modules
  over `f⁻¹O_D`, as a bifunctor. Its action on objects is
  `Stacks.SheafOfModules.inverseImageTensorSheaf` and on morphisms
  `Stacks.SheafOfModules.inverseImageTensorSheafMap`.
* `Stacks.SheafOfModules.inverseImageTensorHomEquiv`: the composite bijection, assembled from the
  four steps `inverseImageTensorStep1` … `inverseImageTensorStep4`.
* `Stacks.SheafOfModules.inverseImageTensorIso`: the natural isomorphism of bifunctors.

## Main results

* `Stacks.SheafOfModules.inverseImageTensorHomEquiv_naturality` and
  `Stacks.SheafOfModules.inverseImageTensorHomEquiv_precomp`: the composite bijection is natural
  in the sheaf of values and in the two source modules.
* `Stacks.SheafOfModules.inverseImageTensorIso_hom_app`: the comparison is the morphism which the
  chain carries to the identity.

## Implementation notes

The four steps are separate definitions with their types written out, for the reason recorded in
the implementation notes of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor`: the objects at the seams have two
spellings each and the two members of a pair are definitionally equal only at *default*
transparency, so a single `Equiv.trans` elaborates but is opaque to `rw` and to `simp`. Declaring
each step at one chosen spelling absorbs those equalities into the declared types once.

The tensor product over `f⁻¹O_D` is `Stacks.SheafOfModules.inverseImageTensorSheaf`, i.e.
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` and not
`AlgebraicGeometry.SheafOfModules.tensorSheafBifunctor`: the inverse image `f⁻¹O_D` of the
structure sheaf of the target is available only as a presheaf of commutative rings together with
the sheaf condition on its underlying presheaf of rings, which is the input the former takes.
`inverseImageTensorBifunctor` packages it as a bifunctor; its functoriality is that of
sheafification composed with that of the monoidal product of presheaves of modules.

The identification of the comparison of Stacks 03EL with this comparison followed by the
comparison of Stacks 03CU is in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorFactorization`.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CategoryTheory.Sheaf
open AlgebraicGeometry.SheafOfModules Stacks.Sheaves.RingedToposModules
  Stacks.PresheafOfModules.ChangeOfRings
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

namespace Stacks.SheafOfModules

universe w w' v u v' u'

section InverseImageChain

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : RingedToposHom X Y)

/-! ### The tensor product over the inverse image of the structure sheaf, as a bifunctor -/

/-- **The tensor product of sheaves of modules over the inverse image `f⁻¹O_D` of the structure
sheaf of the target, as a bifunctor.** It is the tensor bifunctor of Tag 0GMW over `f⁻¹O_D` read
as a sheaf of commutative rings, with its source and target ascribed at the
`Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf` spelling of the sheaf of rings.

The ascription is the discipline of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensor`: the underlying sheaf of rings of
`Stacks.Sheaves.RingedToposModules.inverseImageStructureCommRingSheaf` *is* the inverse-image
sheaf of rings (`commRingSheafToRingSheaf_inverseImageStructureCommRingSheaf`, by `rfl`), but a
statement mixing the two spellings is not type-correct at `implicit` transparency, so the
crossing happens once here. -/
def inverseImageTensorBifunctor :
    SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
        SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor (inverseImageStructureCommRingSheaf f)))

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The bifunctor acts on objects as `Stacks.SheafOfModules.inverseImageTensorSheaf`. -/
lemma inverseImageTensorBifunctor_obj
    (P Q : SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (inverseImageTensorBifunctor f).obj (P, Q) = inverseImageTensorSheaf f P Q :=
  rfl

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- The bifunctor acts on morphisms as `Stacks.SheafOfModules.inverseImageTensorSheafMap`. -/
lemma inverseImageTensorBifunctor_map
    {P P' Q Q' : SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (u : P ⟶ P') (v : Q ⟶ Q') :
    (inverseImageTensorBifunctor f).map ((u, v) : ((P, Q) : _ × _) ⟶ (P', Q')) =
      inverseImageTensorSheafMap f u v :=
  Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    (inverseImageStructureCommRingSheaf f) u v

variable (F F' G G' : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (M M' : SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

/-! ### The four steps -/

/-- **Step 1 of the chain**: `Hom_{f⁻¹O_D}(f⁻¹(F ⊗ G), M) = Hom_{O_D}(F ⊗ G, f_*M)`, the
adjunction of Stacks 03D4 between the inverse image of Stacks 03D2 and the direct image of
Stacks 03D3. -/
def inverseImageTensorStep1 :
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) ⟶ M) ≃
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G) ⟶
        (directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M) :=
  (inverseImageAdjDirectImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).homEquiv _ M

/-- **Step 2 of the chain**: `Hom_{O_D}(F ⊗ G, f_*M) = Bilin_{O_D}(F × G, f_*M)`, the universal
property of the tensor product sheaf over `O_D`. -/
def inverseImageTensorStep2 :
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G) ⟶
        (directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M) ≃
      { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
          moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            ((directImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M) //
        IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q } :=
  (bilinearEquivTensorSheafHom (hA := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property)
    (F := F) (G := G)
    (N := (directImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M)).symm

/-- **Step 3 of the chain**: `Bilin_{O_D}(F × G, f_*M) = Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, M)`, the
step the source of Stacks 03EL calls the interesting one. -/
def inverseImageTensorStep3 :
    { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M) //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q } ≃
      { q : moduleSheaf (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) ⨯
          moduleSheaf (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            ((inverseImageModules f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
          moduleSheaf (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) M //
        IsBilinearPairing (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q } :=
  (inverseImageBilinearEquiv f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F G M).symm

/-- **Step 4 of the chain**:
`Bilin_{f⁻¹O_D}(f⁻¹F × f⁻¹G, M) = Hom_{f⁻¹O_D}(f⁻¹F ⊗_{f⁻¹O_D} f⁻¹G, M)`, the universal property
of the tensor product sheaf over `f⁻¹O_D`. -/
def inverseImageTensorStep4 :
    { q : moduleSheaf (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) ⨯
        moduleSheaf (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
        moduleSheaf (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) M //
      IsBilinearPairing (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q } ≃
      ((Functor.prod (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
          inverseImageTensorBifunctor f).obj (F, G) ⟶ M) :=
  bilinearEquivTensorSheafHom (hA := isSheaf_inverseImageStructureCommRing f)
    (F := (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F)
    (G := (inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) (N := M)

/-- **The chain of bijections.** Morphisms out of the inverse image of a tensor product are
morphisms out of the tensor product, over `f⁻¹O_D`, of the inverse images, in four steps. -/
def inverseImageTensorHomEquiv :
    (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)) ⋙
        inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (F, G) ⟶ M) ≃
      ((Functor.prod (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
        inverseImageTensorBifunctor f).obj (F, G) ⟶ M) :=
  (inverseImageTensorStep1 f F G M).trans ((inverseImageTensorStep2 f F G M).trans
    ((inverseImageTensorStep3 f F G M).trans (inverseImageTensorStep4 f F G M)))

/-! ### Naturality of the four steps in the sheaf of values -/

variable {M M'}

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Step 1 is natural in the sheaf of values. -/
lemma inverseImageTensorStep1_naturality
    (g : (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G)) ⟶ M)
    (k : M ⟶ M') :
    inverseImageTensorStep1 f F G M' (g ≫ k) =
      inverseImageTensorStep1 f F G M g ≫
        (directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map k :=
  (inverseImageAdjDirectImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).homEquiv_naturality_right
    g k

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Step 2 is natural in the sheaf of values. -/
lemma inverseImageTensorStep2_naturality
    (t : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F, G) ⟶
      (directImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M) (k : M ⟶ M') :
    inverseImageTensorStep2 f F G M'
        (t ≫ (directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map k) =
      ⟨(inverseImageTensorStep2 f F G M t).1 ≫
          (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
            ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map k),
        (inverseImageTensorStep2 f F G M t).2.comp
          ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map k)⟩ :=
  bilinearEquivTensorSheafHom_symm_naturality
    (hA := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) t
    ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map k)

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 3 is natural in the sheaf of values. -/
lemma inverseImageTensorStep3_naturality
    (p : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M) //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q }) (k : M ⟶ M') :
    inverseImageTensorStep3 f F G M'
        ⟨p.1 ≫ (moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
            ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map k),
          p.2.comp ((directImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map k)⟩ =
      ⟨(inverseImageTensorStep3 f F G M p).1 ≫
          (moduleSheafFunctor (inverseImageRingSheaf f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map k,
        (inverseImageTensorStep3 f F G M p).2.comp k⟩ :=
  inverseImageBilinearEquiv_symm_naturality f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) p k

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 4 is natural in the sheaf of values. -/
lemma inverseImageTensorStep4_naturality
    (q : { q : moduleSheaf (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) ⨯
        moduleSheaf (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G) ⟶
        moduleSheaf (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) M //
      IsBilinearPairing (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q })
    (k : M ⟶ M') :
    inverseImageTensorStep4 f F G M'
        ⟨q.1 ≫ (moduleSheafFunctor
            (inverseImageRingSheaf f.toToposHom
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map k, q.2.comp k⟩ =
      inverseImageTensorStep4 f F G M q ≫ k :=
  bilinearEquivTensorSheafHom_naturality (hA := isSheaf_inverseImageStructureCommRing f) q k

/-- **The chain is natural in the sheaf of values.** -/
lemma inverseImageTensorHomEquiv_naturality
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)) ⋙
      inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (F, G) ⟶ M) (k : M ⟶ M') :
    inverseImageTensorHomEquiv f F G M' (g ≫ k) =
      inverseImageTensorHomEquiv f F G M g ≫ k := by
  simp only [inverseImageTensorHomEquiv, Equiv.trans_apply]
  rw [inverseImageTensorStep1_naturality, inverseImageTensorStep2_naturality,
    inverseImageTensorStep3_naturality, inverseImageTensorStep4_naturality]

/-! ### Naturality of the four steps in the two source modules -/

variable {F F' G G'}

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Step 1 is natural in the two source modules. -/
lemma inverseImageTensorStep1_precomp (u : F ⟶ F') (v : G ⟶ G')
    (M : SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (g : (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F', G')) ⟶ M) :
    inverseImageTensorStep1 f F G M
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).map (u, v)) ≫ g) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).map (u, v) ≫
        inverseImageTensorStep1 f F' G' M g :=
  (inverseImageAdjDirectImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).homEquiv_naturality_left
    _ g

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Step 2 is natural in the two source modules. -/
lemma inverseImageTensorStep2_precomp (u : F ⟶ F') (v : G ⟶ G')
    (M : SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (t : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).obj (F', G') ⟶
      (directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M) :
    inverseImageTensorStep2 f F G M
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).map (u, v) ≫ t) =
      ⟨prod.map ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u)
            ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v) ≫
          (inverseImageTensorStep2 f F' G' M t).1,
        (inverseImageTensorStep2 f F' G' M t).2.precomp u v⟩ :=
  by
  rw [Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map]
  exact bilinearEquivTensorSheafHom_symm_precomp
    (hA := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).property) t u v

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 3 is natural in the two source modules. -/
lemma inverseImageTensorStep3_precomp (u : F ⟶ F') (v : G ⟶ G')
    (M : SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (p : { q : moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) F' ⨯
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) G' ⟶
        moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
          ((directImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M) //
      IsBilinearPairing (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) q }) :
    inverseImageTensorStep3 f F G M
        ⟨prod.map ((moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u)
            ((moduleSheafFunctor
                (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v) ≫ p.1, p.2.precomp u v⟩ =
      ⟨prod.map ((moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
            ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u))
            ((moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
              ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v)) ≫
          (inverseImageTensorStep3 f F' G' M p).1,
        (inverseImageTensorStep3 f F' G' M p).2.precomp _ _⟩ :=
  inverseImageBilinearEquiv_symm_precomp f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) u v p

omit [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- Step 4 is natural in the two source modules. -/
lemma inverseImageTensorStep4_precomp (u : F ⟶ F') (v : G ⟶ G')
    (M : SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (q : { q : moduleSheaf (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F') ⨯
        moduleSheaf (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G') ⟶
        moduleSheaf (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) M //
      IsBilinearPairing (inverseImageRingSheaf f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q }) :
    inverseImageTensorStep4 f F G M
        ⟨prod.map ((moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
            ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u))
            ((moduleSheafFunctor
              (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
              ((inverseImageModules f.toToposHom
                  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v)) ≫ q.1,
          q.2.precomp _ _⟩ =
      (Functor.prod (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
          inverseImageTensorBifunctor f).map ((u, v) : ((F, G) : _ × _) ⟶ (F', G')) ≫
        inverseImageTensorStep4 f F' G' M q :=
  by
  conv_rhs => rw [Functor.comp_map, Functor.prod_map, inverseImageTensorBifunctor_map]
  exact bilinearEquivTensorSheafHom_precomp (hA := isSheaf_inverseImageStructureCommRing f) q
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map u)
    ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map v)

/-- **The chain is natural in the two source modules.** -/
lemma inverseImageTensorHomEquiv_precomp (u : F ⟶ F') (v : G ⟶ G')
    (M : SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (g : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)) ⋙
      inverseImageModules f.toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj (F', G') ⟶ M) :
    inverseImageTensorHomEquiv f F G M
        ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O))).map (u, v)) ≫ g) =
      (Functor.prod (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
          inverseImageTensorBifunctor f).map (u, v) ≫
        inverseImageTensorHomEquiv f F' G' M g := by
  simp only [inverseImageTensorHomEquiv, Equiv.trans_apply]
  rw [inverseImageTensorStep1_precomp, inverseImageTensorStep2_precomp,
    inverseImageTensorStep3_precomp, inverseImageTensorStep4_precomp]

/-! ### The comparison -/

/-- The inverse of the chain is natural in the sheaf of values. -/
lemma inverseImageTensorHomEquiv_symm_naturality
    (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {M M' : SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (g : (Functor.prod (inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
      inverseImageTensorBifunctor f).obj (F, G) ⟶ M) (k : M ⟶ M') :
    (inverseImageTensorHomEquiv f F G M').symm (g ≫ k) =
      (inverseImageTensorHomEquiv f F G M).symm g ≫ k :=
  (Equiv.symm_apply_eq _).2 (by
    rw [inverseImageTensorHomEquiv_naturality, Equiv.apply_symm_apply])

/-- The inverse of the chain is natural in the two source modules. -/
lemma inverseImageTensorHomEquiv_symm_precomp
    {F F' G G' : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (u : F ⟶ F') (v : G ⟶ G')
    (M : SheafOfModules.{w} (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (g : (Functor.prod (inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
      inverseImageTensorBifunctor f).obj (F', G') ⟶ M) :
    (inverseImageTensorHomEquiv f F G M).symm
        ((Functor.prod (inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
          inverseImageTensorBifunctor f).map (u, v) ≫ g) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)) ⋙
          inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map (u, v) ≫
        (inverseImageTensorHomEquiv f F' G' M).symm g :=
  (Equiv.symm_apply_eq _).2 ((congrArg _ (Equiv.apply_symm_apply _ _)).symm.trans
    (inverseImageTensorHomEquiv_precomp f u v M _).symm)

/-- **The inverse image of a tensor product of sheaves of modules is the tensor product of the
inverse images.** For a morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)`,

`f⁻¹(F ⊗_{O_D} G) ≅ f⁻¹F ⊗_{f⁻¹O_D} f⁻¹G`,

naturally in `F` and in `G`. The comparison is the one determined by the chain of bijections
`Stacks.SheafOfModules.inverseImageTensorHomEquiv`.

This is the factor of the comparison of Stacks 03EL which belongs to the inverse image of
Stacks 03D2; the other factor is the base change of Stacks 03CU. -/
@[sga "4 V 1.6.2" "special case"]
def inverseImageTensorIso :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)) ⋙
        inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ≅
      Functor.prod (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
        inverseImageTensorBifunctor f :=
  Functor.natIsoOfHomEquiv (fun FG M ↦ (inverseImageTensorHomEquiv f FG.1 FG.2 M).symm)
    (fun FG _ _ k g ↦ inverseImageTensorHomEquiv_symm_naturality f FG.1 FG.2 g k)
    (fun uv M g ↦ by
      obtain ⟨u, v⟩ := uv
      exact inverseImageTensorHomEquiv_symm_precomp f u v M g)

/-- The comparison is the morphism which the chain of bijections carries to the identity. -/
lemma inverseImageTensorIso_hom_app
    (F G : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (inverseImageTensorIso f).hom.app (F, G) =
      (inverseImageTensorHomEquiv f F G
          ((Functor.prod (inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
              (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
            inverseImageTensorBifunctor f).obj (F, G))).symm
        (𝟙 ((Functor.prod (inverseImageModules f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
            (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⋙
          inverseImageTensorBifunctor f).obj (F, G))) := rfl

end InverseImageChain

end Stacks.SheafOfModules

end
