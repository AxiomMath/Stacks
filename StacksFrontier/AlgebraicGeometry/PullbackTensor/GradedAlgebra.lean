module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.Bilinear
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso

/-!
# Pullback of a sheaf of graded algebras along a morphism of ringed spaces

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `A` be a sheaf of `ℤ`-graded
`𝒪_Y`-algebras in the sense of [Stacks, Tag 0FQW]. Then `f^*A` is a sheaf of `ℤ`-graded
`𝒪_X`-algebras: the pieces are the pullbacks of the pieces, the multiplication is the pullback
of the multiplication, and the unit is the image of the unit under the unit of the pullback
adjunction.

The multiplication is supplied by
`StacksFrontier/AlgebraicGeometry/PullbackTensor/Bilinear.lean`, i.e. by [Stacks, Tag 01CD].
**The content of this file is the three laws** — associativity and the two unit laws. These are
statements about *arbitrary* local sections of `f^*A`, and
`RingedSpaceModuleAdjunction.modulePullback` is defined as `(modulePushforward f).leftAdjoint`
and has no description of its sections, so they do not follow from the computation of the
multiplication on pullback-unit images. They are proved by passing to stalks:

* a section of a sheaf is determined by its germs (`Stacks.RingedSpace.section_ext_grpGerm`);
* the germ of a product of sections is a function of the germs of the factors, because a
  bilinear map of sheaves of modules factors through the sheafified tensor product
  (`Stacks.RingedSpace.stalkMul` and `stalkMul_grpGerm`);
* the stalk of `f^*G` at `p` is `𝒪_{X,p} ⊗_{𝒪_{Y,f p}} G_{f p}` by [Stacks, Tag 0098], hence is
  generated over `𝒪_{X,p}` by the germs of pullback-unit images
  (`Stacks.RingedSpace.pullbackStalk_linearMap_ext`);
* and on those germs each law is the corresponding law of `A`.

The route through the monoidal structure on sheaves of modules is **not** available: that
structure is produced by localization, so its associator and unitors are not given by formulas
on pure tensors, and the associator formula would be needed in both translation directions.

## Main definitions

* `Stacks.RingedSpace.stalkBilin` and `Stacks.RingedSpace.stalkMul`: the map induced on stalks
  by a bilinear map of sheaves of modules, and the resulting multiplication of germs.
* `Stacks.RingedSpace.sheafCast`: transport of a stalk along an equality of sheaves of modules,
  used to compare the two sides of a law, which live in pieces of propositionally — not
  definitionally — equal degree.
* `Stacks.RingedSpace.pullbackSectionsUnit`: a global section of `f^*M` from a global section
  of `M`.
* `Stacks.RingedSpace.pullbackGradedAlgebra`: **the pulled-back sheaf of graded algebras.**

## Main results

* `Stacks.RingedSpace.section_ext_grpGerm`: a section of a sheaf of modules on a ringed space is
  determined by its germs.
* `Stacks.RingedSpace.stalkMul_grpGerm`: the germ of a product is the product of the germs.
* `Stacks.RingedSpace.pullbackStalk_linearMap_ext`: **stalkwise generation.** Two linear maps
  out of the stalk of `f^*G` agreeing on the germs of pullback-unit images are equal.
* `Stacks.RingedSpace.pullbackMul_assoc`, `pullbackMul_one_mul` and `pullbackMul_mul_one`: the
  three laws.
* `Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit` and
  `pullbackGradedAlgebra_one_eval`: the identification of the pulled-back algebra, i.e. that the
  product of the images of two homogeneous sections is the image of their product and that the
  unit is the image of the unit.

## Implementation notes

The laws are stated with `HEq` because the two sides live in the pieces of two propositionally
equal degrees. Each is reduced to a plain equality by `heq_of_sheafCast_grpGerm`, which
`subst`s the equality of the two pieces and then applies germ extensionality; the degree
transport is therefore never a `cast` on a section and never leaves the proof.

The generation argument is run one variable at a time: for associativity, four steps, with the
three germs successively specialised to germs of pullback-unit images, and a final step in
which the three sections are restricted to the intersection of their three opens.

The chosen stalk isomorphism of [Stacks, Tag 0098] is
`Stacks.RingedSpace.pullbackStalkEquiv`, together with its germ formula
`Stacks.RingedSpace.pullbackStalkEquiv_germ`, both from
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparisonIso.lean`. That is the
only thing this file uses the stalk formula for, and the germ formula is the only property of
the choice that the generation argument needs.

No transparency overrides are used. Scalars and sections are written in
the spellings `Bilinear.lean` already uses.

## References

* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace PresheafOfModules Opposite
open scoped TensorProduct
universe u

namespace Stacks.RingedSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction

section SectionExt

variable {X : RingedSpace.{u, u}}

/-- A section of a sheaf of modules on a ringed space is determined by its germs. -/
lemma section_ext_grpGerm (M : SheafOfModules.{u} (structureRingSheaf X))
    (U : Opens X.carrier) (s t : M.val.obj (op U))
    (h : ∀ (p : X.carrier) (hp : p ∈ U),
      grpGerm X M.val p U hp s = grpGerm X M.val p U hp t) :
    s = t :=
  TopCat.Presheaf.section_ext ((SheafOfModules.toSheaf (structureRingSheaf X)).obj M) U s t h

end SectionExt

section StalkMul

variable {X : RingedSpace.{u, u}} {A B C : SheafOfModules.{u} (structureRingSheaf X)}

/-- The map induced on stalks by a bilinear map of sheaves of modules. -/
noncomputable def stalkBilin (β : SheafOfModules.BilinearMap A B C) (p : X.carrier) :
    grpStalk X A.val p ⊗[ringStalk X p] grpStalk X B.val p →ₗ[ringStalk X p]
      grpStalk X C.val p := by
  let tensorProduct :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (⟨X.presheaf, X.IsSheaf⟩ : Sheaf (JX X) CommRingCat.{u})).obj A).obj B
  letI := stalkModule X tensorProduct.val p
  exact (stalkMapL X tensorProduct.val C.val (ofBilinearSheaf β).val p).comp
    (tensorStalkEquiv p A B).symm.toLinearMap

/-- The multiplication of germs induced by a bilinear map of sheaves of modules. -/
noncomputable def stalkMul (β : SheafOfModules.BilinearMap A B C) (p : X.carrier)
    (m : grpStalk X A.val p) (n : grpStalk X B.val p) : grpStalk X C.val p :=
  stalkBilin β p (m ⊗ₜ[ringStalk X p] n)

/-- **The germ of a product is the product of the germs.** -/
lemma stalkMul_grpGerm (β : SheafOfModules.BilinearMap A B C) (p : X.carrier)
    (U : Opens X.carrier) (hp : p ∈ U) (x : A.val.obj (op U)) (y : B.val.obj (op U)) :
    stalkMul β p (grpGerm X A.val p U hp x) (grpGerm X B.val p U hp y) =
      grpGerm X C.val p U hp (β.app (op U) x y) := by
  show stalkMapL X _ _ (ofBilinearSheaf β).val p ((tensorStalkEquiv p A B).symm _) = _
  rw [(LinearEquiv.symm_apply_eq _).2 (tensorStalkEquiv_germ p A B U hp x y).symm]
  exact (Stacks.SheafOfModules.stalkMapL_germ X (ofBilinearSheaf β).val p U hp _).trans
    (congrArg _ (ofBilinearSheaf_unit_tmul β (op U) x y))

/-- The multiplication of germs is additive in the left factor. -/
lemma stalkMul_add_left (β : SheafOfModules.BilinearMap A B C) (p : X.carrier)
    (m m' : grpStalk X A.val p) (n : grpStalk X B.val p) :
    stalkMul β p (m + m') n = stalkMul β p m n + stalkMul β p m' n := by
  show stalkBilin β p ((m + m') ⊗ₜ[ringStalk X p] n) =
    stalkBilin β p (m ⊗ₜ[ringStalk X p] n) + stalkBilin β p (m' ⊗ₜ[ringStalk X p] n)
  rw [TensorProduct.add_tmul, map_add]

/-- The multiplication of germs is additive in the right factor. -/
lemma stalkMul_add_right (β : SheafOfModules.BilinearMap A B C) (p : X.carrier)
    (m : grpStalk X A.val p) (n n' : grpStalk X B.val p) :
    stalkMul β p m (n + n') = stalkMul β p m n + stalkMul β p m n' := by
  show stalkBilin β p (m ⊗ₜ[ringStalk X p] (n + n')) =
    stalkBilin β p (m ⊗ₜ[ringStalk X p] n) + stalkBilin β p (m ⊗ₜ[ringStalk X p] n')
  rw [TensorProduct.tmul_add, map_add]

/-- The multiplication of germs is linear over the stalk ring in the left factor. -/
lemma stalkMul_smul_left (β : SheafOfModules.BilinearMap A B C) (p : X.carrier)
    (r : ringStalk X p) (m : grpStalk X A.val p) (n : grpStalk X B.val p) :
    stalkMul β p (r • m) n = r • stalkMul β p m n := by
  show stalkBilin β p ((r • m) ⊗ₜ[ringStalk X p] n) = r • stalkBilin β p (m ⊗ₜ[ringStalk X p] n)
  exact (congrArg (stalkBilin β p) (TensorProduct.smul_tmul' r m n).symm).trans
    (map_smul _ _ _)

/-- The multiplication of germs is linear over the stalk ring in the right factor. -/
lemma stalkMul_smul_right (β : SheafOfModules.BilinearMap A B C) (p : X.carrier)
    (r : ringStalk X p) (m : grpStalk X A.val p) (n : grpStalk X B.val p) :
    stalkMul β p m (r • n) = r • stalkMul β p m n := by
  show stalkBilin β p (m ⊗ₜ[ringStalk X p] (r • n)) = r • stalkBilin β p (m ⊗ₜ[ringStalk X p] n)
  exact (congrArg (stalkBilin β p) (TensorProduct.tmul_smul r m n)).trans (map_smul _ _ _)

/-- Multiplication by a fixed germ on the right, as a linear map. -/
noncomputable def stalkMulRight (β : SheafOfModules.BilinearMap A B C) (p : X.carrier)
    (n : grpStalk X B.val p) : grpStalk X A.val p →ₗ[ringStalk X p] grpStalk X C.val p where
  toFun m := stalkMul β p m n
  map_add' m m' := stalkMul_add_left β p m m' n
  map_smul' r m := stalkMul_smul_left β p r m n

/-- Multiplication by a fixed germ on the left, as a linear map. -/
noncomputable def stalkMulLeft (β : SheafOfModules.BilinearMap A B C) (p : X.carrier)
    (m : grpStalk X A.val p) : grpStalk X B.val p →ₗ[ringStalk X p] grpStalk X C.val p where
  toFun n := stalkMul β p m n
  map_add' n n' := stalkMul_add_right β p m n n'
  map_smul' r n := stalkMul_smul_right β p r m n

/-- `stalkMulRight β p n` sends `m` to the product of `m` and `n`. -/
@[simp] lemma stalkMulRight_apply (β : SheafOfModules.BilinearMap A B C) (p : X.carrier)
    (n : grpStalk X B.val p) (m : grpStalk X A.val p) : stalkMulRight β p n m = stalkMul β p m n :=
  rfl

/-- `stalkMulLeft β p m` sends `n` to the product of `m` and `n`. -/
@[simp] lemma stalkMulLeft_apply (β : SheafOfModules.BilinearMap A B C) (p : X.carrier)
    (m : grpStalk X A.val p) (n : grpStalk X B.val p) : stalkMulLeft β p m n = stalkMul β p m n :=
  rfl

end StalkMul

section Transport

variable {X : RingedSpace.{u, u}}

/-- Transport of a stalk along an equality of sheaves of modules. -/
noncomputable def sheafCast {M N : SheafOfModules.{u} (structureRingSheaf X)} (hMN : M = N)
    (p : X.carrier) : grpStalk X M.val p ≃ₗ[ringStalk X p] grpStalk X N.val p :=
  hMN ▸ LinearEquiv.refl (ringStalk X p) (grpStalk X M.val p)

/-- Transport of a stalk along `rfl` is the identity. -/
@[simp] lemma sheafCast_rfl (M : SheafOfModules.{u} (structureRingSheaf X)) (p : X.carrier) :
    sheafCast (rfl : M = M) p = LinearEquiv.refl (ringStalk X p) (grpStalk X M.val p) := rfl

/-- **Two sections of possibly different (but equal) sheaves of modules are heterogeneously
equal once their germs are.** This is `section_ext_grpGerm` in the form the graded-algebra laws
need, where the two sides live in the pieces of two propositionally equal degrees. -/
theorem heq_of_sheafCast_grpGerm {M N : SheafOfModules.{u} (structureRingSheaf X)} (hMN : M = N)
    (U : Opens X.carrier) (s : M.val.obj (op U)) (t : N.val.obj (op U))
    (h : ∀ (p : X.carrier) (hp : p ∈ U),
      sheafCast hMN p (grpGerm X M.val p U hp s) = grpGerm X N.val p U hp t) :
    HEq s t := by
  subst hMN
  exact heq_of_eq (section_ext_grpGerm M U s t h)

end Transport

section Generation

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Stalkwise generation for a pullback.** Two linear maps out of the stalk of `f^*G` which
agree on the germs of the pullback-unit images of local sections of `G` are equal. This is the
one input the graded-algebra laws need, and it is a consequence of the unconditional stalk
formula of [Stacks, Tag 0098]: the stalk is `𝒪_{X,p} ⊗_{𝒪_{Y,f p}} G_{f p}`, which is generated
over `𝒪_{X,p}` by the elements `1 ⊗ t`, and `1 ⊗ t` is the image of such a germ. -/
theorem pullbackStalk_linearMap_ext (G : SheafOfModules.{u} (structureRingSheaf Y))
    (p : X.carrier) {P : Type u} [AddCommGroup P] [Module (ringStalk X p) P]
    (l r : grpStalk X ((pullbackFunctor f).obj G).val p →ₗ[ringStalk X p] P)
    (h : ∀ (V : Opens Y.carrier) (hx : f.hom.base p ∈ V) (s : G.val.obj (op V)),
      l (grpGerm X ((pullbackFunctor f).obj G).val p ((opensMap f).obj V) hx
          (pullbackUnit f G (op V) s)) =
        r (grpGerm X ((pullbackFunctor f).obj G).val p ((opensMap f).obj V) hx
          (pullbackUnit f G (op V) s))) :
    l = r := by
  let _ : Algebra (ringStalk Y (f.hom.base p)) (ringStalk X p) :=
    (f.hom.stalkMap p).hom.toAlgebra
  refine linearMap_ext_of_baseChange_generators (pullbackStalkEquiv f G p) l r fun m ↦ ?_
  obtain ⟨V, hx, s, hs⟩ := Stacks.SheafOfModules.exists_grpGerm_eq Y G.val (f.hom.base p) m
  rw [(LinearEquiv.symm_apply_eq _).2
    ((pullbackStalkEquiv_germ f G p V hx s).trans (congrArg _ hs)).symm]
  exact h V hx s

/-- Two linear maps out of the stalk of `f^*G`, one followed by a transport along an equality of
sheaves, agree as soon as they agree on germs of pullback-unit images. -/
private theorem sheafCast_apply_eq_of_pullbackUnit (G : SheafOfModules.{u} (structureRingSheaf Y))
    (p : X.carrier) {M N : SheafOfModules.{u} (structureRingSheaf X)} (e : M = N)
    (μ : grpStalk X ((pullbackFunctor f).obj G).val p →ₗ[ringStalk X p] grpStalk X M.val p)
    (ν : grpStalk X ((pullbackFunctor f).obj G).val p →ₗ[ringStalk X p] grpStalk X N.val p)
    (h : ∀ (V : Opens Y.carrier) (hx : f.hom.base p ∈ V) (s : G.val.obj (op V)),
      sheafCast e p (μ (grpGerm X ((pullbackFunctor f).obj G).val p ((opensMap f).obj V) hx
          (pullbackUnit f G (op V) s))) =
        ν (grpGerm X ((pullbackFunctor f).obj G).val p ((opensMap f).obj V) hx
          (pullbackUnit f G (op V) s)))
    (g : grpStalk X ((pullbackFunctor f).obj G).val p) :
    sheafCast e p (μ g) = ν g :=
  LinearMap.congr_fun (pullbackStalk_linearMap_ext f G p ((sheafCast e p).toLinearMap.comp μ) ν h) g

end Generation

section PullbackAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The pullback-unit image of the global value of a global section, over the whole space.
`(opensMap f).obj ⊤` is `⊤`, so this is a section of `f^*M` over all of `X`. -/
noncomputable def pullbackUnitTop (M : SheafOfModules.{u} (structureRingSheaf Y))
    (t : M.sections) : ((pullbackFunctor f).obj M).val.obj (op (⊤ : Opens X.carrier)) :=
  pullbackUnit f M (op ⊤) (t.eval (op ⊤))

/-- The global section of `f^*M` obtained from a global section of `M`: the pullback-unit image
over the whole space, restricted to every open. -/
noncomputable def pullbackSectionsUnit (M : SheafOfModules.{u} (structureRingSheaf Y))
    (t : M.sections) : ((pullbackFunctor f).obj M).val.sections :=
  ((pullbackFunctor f).obj M).val.sectionsMk
    (fun U => ((pullbackFunctor f).obj M).val.map
      (homOfLE (le_top : U.unop ≤ (⊤ : Opens X.carrier))).op (pullbackUnitTop f M t))
    (fun {U _V} g =>
      (PresheafOfModules.map_comp_apply ((pullbackFunctor f).obj M).val
          (homOfLE (le_top : U.unop ≤ (⊤ : Opens X.carrier))).op g
          (pullbackUnitTop f M t)).symm.trans
        (PresheafOfModules.congr_map_apply ((pullbackFunctor f).obj M).val
          (Subsingleton.elim _ _) (pullbackUnitTop f M t)))

/-- The value of `pullbackSectionsUnit` over the preimage of an open of `Y` is the
pullback-unit image of the value there. -/
lemma pullbackSectionsUnit_eval (M : SheafOfModules.{u} (structureRingSheaf Y))
    (t : M.sections) (V : Opens Y.carrier) :
    (pullbackSectionsUnit f M t).eval (op ((opensMap f).obj V)) =
      pullbackUnit f M (op V) (t.eval (op V)) := by
  refine (PresheafOfModules.congr_map_apply ((pullbackFunctor f).obj M).val
    (Subsingleton.elim (homOfLE (le_top : (opensMap f).obj V ≤ (⊤ : Opens X.carrier))).op
      ((opensMap f).op.map (homOfLE (le_top : V ≤ ⊤)).op)) (pullbackUnitTop f M t)).trans ?_
  exact (pullbackUnit_restrict f M (homOfLE (le_top : V ≤ ⊤)).op (t.eval (op ⊤))).trans
    (congrArg _ (PresheafOfModules.sections_property t (homOfLE (le_top : V ≤ ⊤)).op))

/-- Germ of a pullback-unit image, after restricting the section to a smaller open. -/
public lemma grpGerm_pullbackUnit_restrict (M : SheafOfModules.{u} (structureRingSheaf Y))
    (p : X.carrier) {V W : Opens Y.carrier} (hWV : W ≤ V) (hx : f.hom.base p ∈ W)
    (a : M.val.obj (op V)) :
    grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj W) hx
        (pullbackUnit f M (op W) (M.val.map (homOfLE hWV).op a)) =
      grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) (hWV hx)
        (pullbackUnit f M (op V) a) := by
  have h1 : pullbackUnit f M (op W) (M.val.map (homOfLE hWV).op a) =
      ((pullbackFunctor f).obj M).val.map ((opensMap f).map (homOfLE hWV)).op
        (pullbackUnit f M (op V) a) :=
    (pullbackUnit_restrict f M (homOfLE hWV).op a).symm
  rw [h1]
  exact TopCat.Presheaf.germ_res_apply ((pullbackFunctor f).obj M).val.presheaf
    ((opensMap f).map (homOfLE hWV)) p hx (pullbackUnit f M (op V) a)

/-- The germ of `pullbackSectionsUnit` is the germ of the global pullback-unit image. -/
private lemma grpGerm_pullbackSectionsUnit (M : SheafOfModules.{u} (structureRingSheaf Y))
    (t : M.sections) (p : X.carrier) (U : Opens X.carrier) (hp : p ∈ U) :
    grpGerm X ((pullbackFunctor f).obj M).val p U hp
        ((pullbackSectionsUnit f M t).eval (op U)) =
      grpGerm X ((pullbackFunctor f).obj M).val p ⊤ (Set.mem_univ p)
        (pullbackUnitTop f M t) :=
  TopCat.Presheaf.germ_res_apply ((pullbackFunctor f).obj M).val.presheaf
    (homOfLE (le_top : U ≤ ⊤)) p hp (pullbackUnitTop f M t)

/-- The germ of the global unit is the germ of the pullback-unit image of the value of the
global section over any open containing the image point. -/
private lemma grpGerm_pullbackUnitTop (M : SheafOfModules.{u} (structureRingSheaf Y))
    (t : M.sections) (p : X.carrier) (V : Opens Y.carrier) (hx : f.hom.base p ∈ V) :
    grpGerm X ((pullbackFunctor f).obj M).val p ⊤ (Set.mem_univ p) (pullbackUnitTop f M t) =
      grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hx
        (pullbackUnit f M (op V) (t.eval (op V))) :=
  (grpGerm_pullbackSectionsUnit f M t p ((opensMap f).obj V) hx).symm.trans
    (congrArg _ (pullbackSectionsUnit_eval f M t V))

variable (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Y))

/-- The germ at `p` of the pulled-back product of two pullback-unit images. -/
lemma stalkMul_pullbackBilinear_germ {M N P : SheafOfModules.{u} (structureRingSheaf Y)}
    (β : SheafOfModules.BilinearMap M N P) (p : X.carrier) (V : Opens Y.carrier)
    (hx : f.hom.base p ∈ V) (a : M.val.obj (op V)) (b : N.val.obj (op V)) :
    stalkMul (pullbackBilinear f β) p
        (grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hx
          (pullbackUnit f M (op V) a))
        (grpGerm X ((pullbackFunctor f).obj N).val p ((opensMap f).obj V) hx
          (pullbackUnit f N (op V) b)) =
      grpGerm X ((pullbackFunctor f).obj P).val p ((opensMap f).obj V) hx
        (pullbackUnit f P (op V) (β.app (op V) a b)) :=
  (stalkMul_grpGerm (pullbackBilinear f β) p ((opensMap f).obj V) hx _ _).trans
    (congrArg _ (pullbackBilinear_pullbackUnit f β (op V) a b))

/-- The transport of a germ of a pullback-unit image along an equality of the sheaves. -/
lemma sheafCast_germ_pullbackUnit {M N : SheafOfModules.{u} (structureRingSheaf Y)}
    (hMN : M = N) (p : X.carrier) (V : Opens Y.carrier) (hx : f.hom.base p ∈ V)
    (a : M.val.obj (op V)) (b : N.val.obj (op V)) (hab : HEq a b) :
    sheafCast (congrArg (pullbackFunctor f).obj hMN) p
        (grpGerm X ((pullbackFunctor f).obj M).val p ((opensMap f).obj V) hx
          (pullbackUnit f M (op V) a)) =
      grpGerm X ((pullbackFunctor f).obj N).val p ((opensMap f).obj V) hx
        (pullbackUnit f N (op V) b) := by
  subst hMN
  obtain rfl := eq_of_heq hab
  rfl

/-! ### Associativity -/

/-- Associativity of the pulled-back multiplication, on germs of pullback-unit images of
sections over one common open. -/
private lemma assoc_stalk_common (i j k : ℤ) (p : X.carrier) (V : Opens Y.carrier)
    (hx : f.hom.base p ∈ V) (a : (A.piece i).val.obj (op V)) (b : (A.piece j).val.obj (op V))
    (c : (A.piece k).val.obj (op V)) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_assoc i j k)) p
        (stalkMul (pullbackBilinear f (A.mul (i + j) k)) p
          (stalkMul (pullbackBilinear f (A.mul i j)) p
            (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj V) hx
              (pullbackUnit f (A.piece i) (op V) a))
            (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj V) hx
              (pullbackUnit f (A.piece j) (op V) b)))
          (grpGerm X ((pullbackFunctor f).obj (A.piece k)).val p ((opensMap f).obj V) hx
            (pullbackUnit f (A.piece k) (op V) c))) =
      stalkMul (pullbackBilinear f (A.mul i (j + k))) p
        (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj V) hx
          (pullbackUnit f (A.piece i) (op V) a))
        (stalkMul (pullbackBilinear f (A.mul j k)) p
          (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj V) hx
            (pullbackUnit f (A.piece j) (op V) b))
          (grpGerm X ((pullbackFunctor f).obj (A.piece k)).val p ((opensMap f).obj V) hx
            (pullbackUnit f (A.piece k) (op V) c))) := by
  rw [stalkMul_pullbackBilinear_germ, stalkMul_pullbackBilinear_germ,
    stalkMul_pullbackBilinear_germ, stalkMul_pullbackBilinear_germ]
  exact sheafCast_germ_pullbackUnit f (congrArg A.piece (add_assoc i j k)) p V hx _ _
    (A.mul_assoc i j k (op V) a b c)

/-- Associativity of the pulled-back multiplication, on germs of pullback-unit images of
sections over three possibly different opens. -/
private lemma assoc_stalk_gen (i j k : ℤ) (p : X.carrier)
    (Va Vb Vc : Opens Y.carrier) (ha : f.hom.base p ∈ Va) (hb : f.hom.base p ∈ Vb)
    (hc : f.hom.base p ∈ Vc) (a : (A.piece i).val.obj (op Va))
    (b : (A.piece j).val.obj (op Vb)) (c : (A.piece k).val.obj (op Vc)) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_assoc i j k)) p
        (stalkMul (pullbackBilinear f (A.mul (i + j) k)) p
          (stalkMul (pullbackBilinear f (A.mul i j)) p
            (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
              (pullbackUnit f (A.piece i) (op Va) a))
            (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj Vb) hb
              (pullbackUnit f (A.piece j) (op Vb) b)))
          (grpGerm X ((pullbackFunctor f).obj (A.piece k)).val p ((opensMap f).obj Vc) hc
            (pullbackUnit f (A.piece k) (op Vc) c))) =
      stalkMul (pullbackBilinear f (A.mul i (j + k))) p
        (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
          (pullbackUnit f (A.piece i) (op Va) a))
        (stalkMul (pullbackBilinear f (A.mul j k)) p
          (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj Vb) hb
            (pullbackUnit f (A.piece j) (op Vb) b))
          (grpGerm X ((pullbackFunctor f).obj (A.piece k)).val p ((opensMap f).obj Vc) hc
            (pullbackUnit f (A.piece k) (op Vc) c))) := by
  have hxW : f.hom.base p ∈ Va ⊓ Vb ⊓ Vc := ⟨⟨ha, hb⟩, hc⟩
  rw [← grpGerm_pullbackUnit_restrict f (A.piece i)
      p (le_trans inf_le_left inf_le_left : Va ⊓ Vb ⊓ Vc ≤ Va) hxW a,
    ← grpGerm_pullbackUnit_restrict f (A.piece j)
      p (le_trans inf_le_left inf_le_right : Va ⊓ Vb ⊓ Vc ≤ Vb) hxW b,
    ← grpGerm_pullbackUnit_restrict f (A.piece k)
      p (inf_le_right : Va ⊓ Vb ⊓ Vc ≤ Vc) hxW c]
  exact assoc_stalk_common f A i j k p (Va ⊓ Vb ⊓ Vc) hxW _ _ _

/-- Associativity of the pulled-back multiplication on stalks, in the third variable
arbitrary. -/
private lemma assoc_stalk_z (i j k : ℤ) (p : X.carrier)
    (Va Vb : Opens Y.carrier) (ha : f.hom.base p ∈ Va) (hb : f.hom.base p ∈ Vb)
    (a : (A.piece i).val.obj (op Va)) (b : (A.piece j).val.obj (op Vb))
    (gz : grpStalk X ((pullbackFunctor f).obj (A.piece k)).val p) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_assoc i j k)) p
        (stalkMul (pullbackBilinear f (A.mul (i + j) k)) p
          (stalkMul (pullbackBilinear f (A.mul i j)) p
            (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
              (pullbackUnit f (A.piece i) (op Va) a))
            (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj Vb) hb
              (pullbackUnit f (A.piece j) (op Vb) b))) gz) =
      stalkMul (pullbackBilinear f (A.mul i (j + k))) p
        (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
          (pullbackUnit f (A.piece i) (op Va) a))
        (stalkMul (pullbackBilinear f (A.mul j k)) p
          (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj Vb) hb
            (pullbackUnit f (A.piece j) (op Vb) b)) gz) := by
  set gx := grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
    (pullbackUnit f (A.piece i) (op Va) a) with hgx
  set gy := grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj Vb) hb
    (pullbackUnit f (A.piece j) (op Vb) b) with hgy
  exact sheafCast_apply_eq_of_pullbackUnit f (A.piece k) p _
    (stalkMulLeft (pullbackBilinear f (A.mul (i + j) k)) p
      (stalkMul (pullbackBilinear f (A.mul i j)) p gx gy))
    ((stalkMulLeft (pullbackBilinear f (A.mul i (j + k))) p gx).comp
      (stalkMulLeft (pullbackBilinear f (A.mul j k)) p gy))
    (fun Vc hc c => by
      rw [hgx, hgy]
      exact assoc_stalk_gen f A i j k p Va Vb Vc ha hb hc a b c) gz

/-- Associativity of the pulled-back multiplication on stalks, in the second and third
variables arbitrary. -/
private lemma assoc_stalk_y (i j k : ℤ) (p : X.carrier)
    (Va : Opens Y.carrier) (ha : f.hom.base p ∈ Va) (a : (A.piece i).val.obj (op Va))
    (gy : grpStalk X ((pullbackFunctor f).obj (A.piece j)).val p)
    (gz : grpStalk X ((pullbackFunctor f).obj (A.piece k)).val p) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_assoc i j k)) p
        (stalkMul (pullbackBilinear f (A.mul (i + j) k)) p
          (stalkMul (pullbackBilinear f (A.mul i j)) p
            (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
              (pullbackUnit f (A.piece i) (op Va) a)) gy) gz) =
      stalkMul (pullbackBilinear f (A.mul i (j + k))) p
        (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
          (pullbackUnit f (A.piece i) (op Va) a))
        (stalkMul (pullbackBilinear f (A.mul j k)) p gy gz) := by
  set gx := grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
    (pullbackUnit f (A.piece i) (op Va) a) with hgx
  exact sheafCast_apply_eq_of_pullbackUnit f (A.piece j) p _
    ((stalkMulRight (pullbackBilinear f (A.mul (i + j) k)) p gz).comp
      (stalkMulLeft (pullbackBilinear f (A.mul i j)) p gx))
    ((stalkMulLeft (pullbackBilinear f (A.mul i (j + k))) p gx).comp
      (stalkMulRight (pullbackBilinear f (A.mul j k)) p gz))
    (fun Vb hb b => by
      rw [hgx]
      exact assoc_stalk_z f A i j k p Va Vb ha hb a b gz) gy

/-- **Associativity of the pulled-back multiplication on stalks.** -/
private lemma assoc_stalk (i j k : ℤ) (p : X.carrier)
    (gx : grpStalk X ((pullbackFunctor f).obj (A.piece i)).val p)
    (gy : grpStalk X ((pullbackFunctor f).obj (A.piece j)).val p)
    (gz : grpStalk X ((pullbackFunctor f).obj (A.piece k)).val p) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_assoc i j k)) p
        (stalkMul (pullbackBilinear f (A.mul (i + j) k)) p
          (stalkMul (pullbackBilinear f (A.mul i j)) p gx gy) gz) =
      stalkMul (pullbackBilinear f (A.mul i (j + k))) p gx
        (stalkMul (pullbackBilinear f (A.mul j k)) p gy
          gz) :=
  sheafCast_apply_eq_of_pullbackUnit f (A.piece i) p _
    ((stalkMulRight (pullbackBilinear f (A.mul (i + j) k)) p gz).comp
      (stalkMulRight (pullbackBilinear f (A.mul i j)) p gy))
    (stalkMulRight (pullbackBilinear f (A.mul i (j + k))) p
      (stalkMul (pullbackBilinear f (A.mul j k)) p gy gz))
    (fun Va ha a => assoc_stalk_y f A i j k p Va ha a gy gz) gx

/-- **Associativity of the pulled-back multiplication.** -/
theorem pullbackMul_assoc (i j k : ℤ) (U : Opens X.carrier)
    (x : ((pullbackFunctor f).obj (A.piece i)).val.obj (op U))
    (y : ((pullbackFunctor f).obj (A.piece j)).val.obj (op U))
    (z : ((pullbackFunctor f).obj (A.piece k)).val.obj (op U)) :
    HEq ((pullbackBilinear f (A.mul (i + j) k)).app (op U)
          ((pullbackBilinear f (A.mul i j)).app (op U) x y) z)
      ((pullbackBilinear f (A.mul i (j + k))).app (op U) x
        ((pullbackBilinear f (A.mul j k)).app (op U) y z)) := by
  refine heq_of_sheafCast_grpGerm
    (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_assoc i j k)) U _ _
    fun p hp => ?_
  rw [← stalkMul_grpGerm (pullbackBilinear f (A.mul (i + j) k)) p U hp _ z,
    ← stalkMul_grpGerm (pullbackBilinear f (A.mul i j)) p U hp x y,
    ← stalkMul_grpGerm (pullbackBilinear f (A.mul i (j + k))) p U hp x _,
    ← stalkMul_grpGerm (pullbackBilinear f (A.mul j k)) p U hp y z]
  exact assoc_stalk f A i j k p _ _ _

/-! ### The unit laws -/

/-- The global unit of the pulled-back algebra is a left identity, on stalks. -/
private lemma one_mul_stalk (i : ℤ) (p : X.carrier)
    (gx : grpStalk X ((pullbackFunctor f).obj (A.piece i)).val p) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (zero_add i)) p
        (stalkMul (pullbackBilinear f (A.mul 0 i)) p
          (grpGerm X ((pullbackFunctor f).obj (A.piece 0)).val p ⊤ (Set.mem_univ p)
            (pullbackUnitTop f (A.piece 0) A.one)) gx) = gx :=
  sheafCast_apply_eq_of_pullbackUnit f (A.piece i) p _
    (stalkMulLeft (pullbackBilinear f (A.mul 0 i)) p
      (grpGerm X ((pullbackFunctor f).obj (A.piece 0)).val p ⊤ (Set.mem_univ p)
        (pullbackUnitTop f (A.piece 0) A.one)))
    LinearMap.id
    (fun V hx a => by
      rw [stalkMulLeft_apply, LinearMap.id_apply,
        grpGerm_pullbackUnitTop f (A.piece 0) A.one p V hx, stalkMul_pullbackBilinear_germ]
      exact sheafCast_germ_pullbackUnit f (congrArg A.piece (zero_add i)) p V hx _ _
        (A.one_mul i (op V) a)) gx

/-- The global unit of the pulled-back algebra is a right identity, on stalks. -/
private lemma mul_one_stalk (i : ℤ) (p : X.carrier)
    (gx : grpStalk X ((pullbackFunctor f).obj (A.piece i)).val p) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_zero i)) p
        (stalkMul (pullbackBilinear f (A.mul i 0)) p gx
          (grpGerm X ((pullbackFunctor f).obj (A.piece 0)).val p ⊤ (Set.mem_univ p)
            (pullbackUnitTop f (A.piece 0) A.one))) = gx :=
  sheafCast_apply_eq_of_pullbackUnit f (A.piece i) p _
    (stalkMulRight (pullbackBilinear f (A.mul i 0)) p
      (grpGerm X ((pullbackFunctor f).obj (A.piece 0)).val p ⊤ (Set.mem_univ p)
        (pullbackUnitTop f (A.piece 0) A.one)))
    LinearMap.id
    (fun V hx a => by
      rw [stalkMulRight_apply, LinearMap.id_apply,
        grpGerm_pullbackUnitTop f (A.piece 0) A.one p V hx, stalkMul_pullbackBilinear_germ]
      exact sheafCast_germ_pullbackUnit f (congrArg A.piece (add_zero i)) p V hx _ _
        (A.mul_one i (op V) a)) gx

/-- **The global unit of the pulled-back algebra is a left identity.** -/
theorem pullbackMul_one_mul (i : ℤ) (U : Opens X.carrier)
    (x : ((pullbackFunctor f).obj (A.piece i)).val.obj (op U)) :
    HEq ((pullbackBilinear f (A.mul 0 i)).app (op U)
        ((pullbackSectionsUnit f (A.piece 0) A.one).eval (op U)) x) x := by
  refine heq_of_sheafCast_grpGerm
    (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (zero_add i)) U _ _ fun p hp => ?_
  rw [← stalkMul_grpGerm (pullbackBilinear f (A.mul 0 i)) p U hp _ x,
    grpGerm_pullbackSectionsUnit f (A.piece 0) A.one p U hp]
  exact one_mul_stalk f A i p _

/-- **The global unit of the pulled-back algebra is a right identity.** -/
theorem pullbackMul_mul_one (i : ℤ) (U : Opens X.carrier)
    (x : ((pullbackFunctor f).obj (A.piece i)).val.obj (op U)) :
    HEq ((pullbackBilinear f (A.mul i 0)).app (op U) x
        ((pullbackSectionsUnit f (A.piece 0) A.one).eval (op U))) x := by
  refine heq_of_sheafCast_grpGerm
    (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_zero i)) U _ _ fun p hp => ?_
  rw [← stalkMul_grpGerm (pullbackBilinear f (A.mul i 0)) p U hp x _,
    grpGerm_pullbackSectionsUnit f (A.piece 0) A.one p U hp]
  exact mul_one_stalk f A i p _

/-! ### Commutativity

Commutativity of the homogeneous multiplication is not one of the fields of
`SheafOfModules.GradedAlgebra`, but it is what the ungraded realization needs in order to be a
sheaf of *commutative* rings, so the pulled-back algebra has to be shown to inherit it. The
proof is the generation argument of the three laws, run with two variables instead of three:
a general section of `f^*(A.piece i)` is only locally a pullback-unit image, and the product of
two pullback-unit images is computed by `pullbackGradedAlgebra_mul_pullbackUnit`, so the two
sides are compared on stalks, where the germs of pullback-unit images generate by
[Stacks, Tag 0098]. As for the three laws the two sides live in the pieces of the two
propositionally equal degrees `i + j` and `j + i`, whence the `HEq`. -/

/-- Commutativity of the pulled-back multiplication, on germs of pullback-unit images of two
sections over one common open. -/
private lemma comm_stalk_common
    (hc : ∀ (i j : ℤ) (W : (Opens Y.carrier)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (i j : ℤ) (p : X.carrier) (V : Opens Y.carrier) (hx : f.hom.base p ∈ V)
    (a : (A.piece i).val.obj (op V)) (b : (A.piece j).val.obj (op V)) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_comm i j)) p
        (stalkMul (pullbackBilinear f (A.mul i j)) p
          (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj V) hx
            (pullbackUnit f (A.piece i) (op V) a))
          (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj V) hx
            (pullbackUnit f (A.piece j) (op V) b))) =
      stalkMul (pullbackBilinear f (A.mul j i)) p
        (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj V) hx
          (pullbackUnit f (A.piece j) (op V) b))
        (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj V) hx
          (pullbackUnit f (A.piece i) (op V) a)) := by
  rw [stalkMul_pullbackBilinear_germ, stalkMul_pullbackBilinear_germ]
  exact sheafCast_germ_pullbackUnit f (congrArg A.piece (add_comm i j)) p V hx _ _
    (hc i j (op V) a b)

/-- Commutativity of the pulled-back multiplication, on germs of pullback-unit images of two
sections over two possibly different opens. -/
private lemma comm_stalk_gen
    (hc : ∀ (i j : ℤ) (W : (Opens Y.carrier)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (i j : ℤ) (p : X.carrier) (Va Vb : Opens Y.carrier) (ha : f.hom.base p ∈ Va)
    (hb : f.hom.base p ∈ Vb) (a : (A.piece i).val.obj (op Va))
    (b : (A.piece j).val.obj (op Vb)) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_comm i j)) p
        (stalkMul (pullbackBilinear f (A.mul i j)) p
          (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
            (pullbackUnit f (A.piece i) (op Va) a))
          (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj Vb) hb
            (pullbackUnit f (A.piece j) (op Vb) b))) =
      stalkMul (pullbackBilinear f (A.mul j i)) p
        (grpGerm X ((pullbackFunctor f).obj (A.piece j)).val p ((opensMap f).obj Vb) hb
          (pullbackUnit f (A.piece j) (op Vb) b))
        (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
          (pullbackUnit f (A.piece i) (op Va) a)) := by
  have hxW : f.hom.base p ∈ Va ⊓ Vb := ⟨ha, hb⟩
  rw [← grpGerm_pullbackUnit_restrict f (A.piece i) p (inf_le_left : Va ⊓ Vb ≤ Va) hxW a,
    ← grpGerm_pullbackUnit_restrict f (A.piece j) p (inf_le_right : Va ⊓ Vb ≤ Vb) hxW b]
  exact comm_stalk_common f A hc i j p (Va ⊓ Vb) hxW _ _

/-- Commutativity of the pulled-back multiplication on stalks, in the second variable
arbitrary. -/
private lemma comm_stalk_y
    (hc : ∀ (i j : ℤ) (W : (Opens Y.carrier)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (i j : ℤ) (p : X.carrier) (Va : Opens Y.carrier) (ha : f.hom.base p ∈ Va)
    (a : (A.piece i).val.obj (op Va))
    (gy : grpStalk X ((pullbackFunctor f).obj (A.piece j)).val p) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_comm i j)) p
        (stalkMul (pullbackBilinear f (A.mul i j)) p
          (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
            (pullbackUnit f (A.piece i) (op Va) a)) gy) =
      stalkMul (pullbackBilinear f (A.mul j i)) p gy
        (grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
          (pullbackUnit f (A.piece i) (op Va) a)) := by
  set gx := grpGerm X ((pullbackFunctor f).obj (A.piece i)).val p ((opensMap f).obj Va) ha
    (pullbackUnit f (A.piece i) (op Va) a) with hgx
  exact sheafCast_apply_eq_of_pullbackUnit f (A.piece j) p _
    (stalkMulLeft (pullbackBilinear f (A.mul i j)) p gx)
    (stalkMulRight (pullbackBilinear f (A.mul j i)) p gx)
    (fun Vb hb b => by
      rw [hgx]
      exact comm_stalk_gen f A hc i j p Va Vb ha hb a b) gy

/-- **Commutativity of the pulled-back multiplication on stalks.** -/
private lemma comm_stalk
    (hc : ∀ (i j : ℤ) (W : (Opens Y.carrier)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (i j : ℤ) (p : X.carrier)
    (gx : grpStalk X ((pullbackFunctor f).obj (A.piece i)).val p)
    (gy : grpStalk X ((pullbackFunctor f).obj (A.piece j)).val p) :
    sheafCast (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_comm i j)) p
        (stalkMul (pullbackBilinear f (A.mul i j)) p gx gy) =
      stalkMul (pullbackBilinear f (A.mul j i)) p gy gx :=
  sheafCast_apply_eq_of_pullbackUnit f (A.piece i) p _
    (stalkMulRight (pullbackBilinear f (A.mul i j)) p gy)
    (stalkMulLeft (pullbackBilinear f (A.mul j i)) p gy)
    (fun Va ha a => comm_stalk_y f A hc i j p Va ha a gy) gx

/-- **Commutativity of the pulled-back multiplication.** If the homogeneous multiplication of
`A` is commutative then so is that of `f^*A`. -/
theorem pullbackMul_mul_comm
    (hc : ∀ (i j : ℤ) (W : (Opens Y.carrier)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (i j : ℤ) (U : Opens X.carrier)
    (x : ((pullbackFunctor f).obj (A.piece i)).val.obj (op U))
    (y : ((pullbackFunctor f).obj (A.piece j)).val.obj (op U)) :
    HEq ((pullbackBilinear f (A.mul i j)).app (op U) x y)
      ((pullbackBilinear f (A.mul j i)).app (op U) y x) := by
  refine heq_of_sheafCast_grpGerm
    (congrArg (fun n => (pullbackFunctor f).obj (A.piece n)) (add_comm i j)) U _ _ fun p hp => ?_
  rw [← stalkMul_grpGerm (pullbackBilinear f (A.mul i j)) p U hp x y,
    ← stalkMul_grpGerm (pullbackBilinear f (A.mul j i)) p U hp y x]
  exact comm_stalk f A hc i j p _ _

/-! ### The pulled-back graded algebra -/

/-- **The pullback of a sheaf of graded algebras along a morphism of ringed spaces.** The
pieces are the pullbacks of the pieces, the multiplication is the pullback of the
multiplication of [Stacks, Tag 01CD], and the unit is the pullback-unit image of the unit.
The three laws are checked on stalks: by [Stacks, Tag 0098] the stalk of a pullback is
`𝒪_{X,p} ⊗_{𝒪_{Y,f p}} (-)_{f p}`, hence generated by germs of pullback-unit images, and on
those the laws are the laws of `A`. -/
noncomputable def pullbackGradedAlgebra :
    SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf X) where
  piece n := (pullbackFunctor f).obj (A.piece n)
  mul i j := pullbackBilinear f (A.mul i j)
  one := pullbackSectionsUnit f (A.piece 0) A.one
  mul_assoc i j k U x y z := by
    obtain ⟨U⟩ := U
    exact pullbackMul_assoc f A i j k U x y z
  one_mul i U x := by
    obtain ⟨U⟩ := U
    exact pullbackMul_one_mul f A i U x
  mul_one i U x := by
    obtain ⟨U⟩ := U
    exact pullbackMul_mul_one f A i U x

/-- The degree `n` piece of the pulled-back graded algebra is the pullback of the degree `n`
piece. -/
@[simp] lemma pullbackGradedAlgebra_piece (n : ℤ) :
    (pullbackGradedAlgebra f A).piece n = (pullbackFunctor f).obj (A.piece n) := rfl

/-- The multiplication of the pulled-back graded algebra is the pullback of the multiplication. -/
@[simp] lemma pullbackGradedAlgebra_mul (i j : ℤ) :
    (pullbackGradedAlgebra f A).mul i j = pullbackBilinear f (A.mul i j) := rfl

/-- **The pulled-back multiplication on pullback-unit images.** This is the compatibility that
identifies the pulled-back algebra: the product of the images of two homogeneous sections is
the image of their product. -/
lemma pullbackGradedAlgebra_mul_pullbackUnit (i j : ℤ) (V : Opens Y.carrier)
    (a : (A.piece i).val.obj (op V)) (b : (A.piece j).val.obj (op V)) :
    ((pullbackGradedAlgebra f A).mul i j).app (op ((opensMap f).obj V))
        (pullbackUnit f (A.piece i) (op V) a) (pullbackUnit f (A.piece j) (op V) b) =
      pullbackUnit f (A.piece (i + j)) (op V) ((A.mul i j).app (op V) a b) :=
  pullbackBilinear_pullbackUnit f (A.mul i j) (op V) a b

/-- **The unit of the pulled-back algebra is the image of the unit.** -/
lemma pullbackGradedAlgebra_one_eval (V : Opens Y.carrier) :
    (pullbackGradedAlgebra f A).one.eval (op ((opensMap f).obj V)) =
      pullbackUnit f (A.piece 0) (op V) (A.one.eval (op V)) :=
  pullbackSectionsUnit_eval f (A.piece 0) A.one V

/-- **The homogeneous multiplication of `f^*A` is commutative as soon as that of `A` is.** This
is the datum the ungraded realization of `f^*A` needs in order to be a sheaf of commutative
rings, hence the datum the relative spectrum of `f^*A` needs. -/
theorem pullbackGradedAlgebra_mul_comm
    (hc : ∀ (i j : ℤ) (W : (Opens Y.carrier)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (i j : ℤ) (W : (Opens X.carrier)ᵒᵖ)
    (x : ((pullbackGradedAlgebra f A).piece i).val.obj W)
    (y : ((pullbackGradedAlgebra f A).piece j).val.obj W) :
    HEq (((pullbackGradedAlgebra f A).mul i j).app W x y)
      (((pullbackGradedAlgebra f A).mul j i).app W y x) := by
  obtain ⟨U⟩ := W
  exact pullbackMul_mul_comm f A hc i j U x y

end PullbackAlgebra

end Stacks.RingedSpace

end
