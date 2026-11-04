module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatTensorShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorSymmetry
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.KFlatComplexesDefinition
import StacksCore.Tactic.StacksAttribute

@[expose] public section

/-!
# Two out of three for K-flat complexes in a short exact sequence

Let `(C, O)` be a ringed site and let `0 → K₁ → K₂ → K₃ → 0` be a short exact sequence of
cochain complexes of `O`-modules whose third complex has flat terms.  Then K-flatness of any
two of the three complexes implies K-flatness of the third.

## Main results

* `Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_left_of_shortExact`: K-flatness of the middle and
  the right complex
  implies K-flatness of the left complex.
* `Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_middle_of_shortExact`: K-flatness of the two
  outer complexes implies
  K-flatness of the middle complex.
* `Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_right_of_shortExact`: K-flatness of the left and
  the middle complex
  implies K-flatness of the right complex.

## Implementation notes

The three implications are the three independent cases of the source's assertion, and they
all come from one lemma, `shortExact_tensorComplex`: for a fixed complex `F` of `O`-modules,
the sequence `0 → Tot(F ⊗ K₁) → Tot(F ⊗ K₂) → Tot(F ⊗ K₃) → 0` of total tensor complexes is
again short exact.  Granting that, K-flatness of two of the `Kᵢ` says that two of the three
total complexes are acyclic, and the long exact sequence of cohomology gives acyclicity of
the third; that last step is `acyclic_X₁_of_shortExact`, `ShortComplex.ShortExact.acyclic_X₂`
and `acyclic_X₃_of_shortExact`.

Short exactness of the total complexes is proved degree by degree
(`HomologicalComplex.shortExact_of_degreewise_shortExact`).  In total degree `n` the complex
`Tot(F ⊗ Kᵢ)` is the coproduct of the `F^p ⊗ Kᵢ^q` over `p + q = n`, so the summandwise
statement is that `F^p ⊗ -` keeps `0 → K₁^q → K₂^q → K₃^q → 0` short exact, which is Tag 03EX
read at the flat module `K₃^q` (`shortExact_map_sheafTensor_obj`), and a coproduct of short
exact sequences is short exact because `Mod(O)` satisfies AB4 (`shortExact_coproduct`).

Tag 03EX is available in the tree in the spelling `- ⊗ G`
(`Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj`) and the total
  complex needs the spelling
`G ⊗ -`; the two are identified by the symmetry of the tensor product
(`Stacks.SheafOfModules.Tensor.sheafTensorBraiding`, Mathlib's braiding on presheaves of
  modules carried to sheaves) transported to
short complexes by `ShortComplex.mapNatIso`.  Additivity of `Tot(F ⊗ -)` is the general fact
`Stacks.SheafOfModules.Tensor.Reduction.map₂HomologicalComplex_obj_additive` about
`Functor.map₂HomologicalComplex`, recorded here as an instance.

**Universes.**  The object, morphism and module universes of the site are independent, the one
surviving relation being that the module universe equals the ring universe.  In particular the
three implications apply to a `AlgebraicGeometry.RingedTopos.{u, u + 1, u}` — the shape of
`AlgebraicGeometry.Space.smallEtaleRingedTopos`, whose site is a `Type (u + 1)` while its
structure sheaf has sections in `Type u`.

The statement does not need a small site with all four universes equal.  The
extension-by-zero resolutions that would force such a pin on Tag 03EX are the route of
`Stacks.SheafOfModules.FlatTensorShortExact`, whose own module documentation says it is a
deliberate specialisation; 03EX is *also* carried by
`Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj`, which resolves by the free
presheaf of modules on the presheaf of sections instead and so never meets an extension by
zero.  Reading 03EX off that declaration is the whole of the generalisation here; the rest of
the argument never sees the site.

Two instances have to be supplied rather than inferred once the module universe no longer
contains the object universe of the site.  `J.HasSheafCompose (forget₂ CommRingCat RingCat)`
comes from `Stacks.hasSheafCompose_forget₂_commRingCat`, which holds at every pair of site
universes, rather than from Mathlib's size-restricted instance.  And exactness of the
coproducts the total complex is built from is `hasExactColimitsOfShape_discrete_ofSize`, AB4
shrunk to the shapes in `Type 0` that the antidiagonal index actually uses, rather than
`Stacks.SheafOfModules.FlatCoproduct.hasExactColimitsOfShape_discrete`, which is stated for an
index type in the module universe and needs that universe to contain the site.

## References

* [The Stacks Project, Tag 0G7B](https://stacks.math.columbia.edu/tag/0G7B)
* [The Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [The Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN)
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace Stacks.SheafOfModules.KFlatTwoOutOfThree

/-! ### Short exactness in an abelian category -/

section Abelian

variable {A : Type*} [Category* A] [Abelian A]

/-- **A coproduct of short exact sequences is short exact**, in a category where coproducts of
the given shape are exact.  The three coproducts are given as abstract colimit cofans and the
two maps between their vertices as data compatible with the inclusions, which is the form in
which the total complex of a double complex presents its differentials. -/
theorem shortExact_coproduct {β : Type*}
    [HasColimitsOfShape (Discrete β) A] [HasExactColimitsOfShape (Discrete β) A]
    (T : β → ShortComplex A) (hT : ∀ b, (T b).ShortExact)
    {c₁ : Cofan fun b => (T b).X₁} (hc₁ : IsColimit c₁)
    {c₂ : Cofan fun b => (T b).X₂} (hc₂ : IsColimit c₂)
    {c₃ : Cofan fun b => (T b).X₃} (hc₃ : IsColimit c₃)
    (f : c₁.pt ⟶ c₂.pt) (g : c₂.pt ⟶ c₃.pt) (hfg : f ≫ g = 0)
    (hf : ∀ b, c₁.inj b ≫ f = (T b).f ≫ c₂.inj b)
    (hg : ∀ b, c₂.inj b ≫ g = (T b).g ≫ c₃.inj b) :
    (ShortComplex.mk f g hfg).ShortExact := by
  let X₁ : Discrete β ⥤ A := Discrete.functor fun b => (T b).X₁
  let X₂ : Discrete β ⥤ A := Discrete.functor fun b => (T b).X₂
  let X₃ : Discrete β ⥤ A := Discrete.functor fun b => (T b).X₃
  let sf : X₁ ⟶ X₂ := Discrete.natTrans fun b => (T b.as).f
  let sg : X₂ ⟶ X₃ := Discrete.natTrans fun b => (T b.as).g
  let S : ShortComplex (Discrete β ⥤ A) := ShortComplex.mk sf sg (by ext b; exact (T b.as).zero)
  have hE : JointlyReflectIsomorphisms
      fun b : β => (evaluation (Discrete β) A).obj ⟨b⟩ :=
    ⟨fun f h => have : ∀ x : Discrete β, IsIso (f.app x) := fun ⟨b⟩ => h b
      NatIso.isIso_of_isIso_app f⟩
  have hS : S.Exact := (hE.exact_iff S).2 fun b => (hT b).exact
  have : ∀ b : Discrete β, Mono (sf.app b) := fun ⟨b⟩ => (hT b).mono_f
  have : ∀ b : Discrete β, Epi (sg.app b) := fun ⟨b⟩ => (hT b).epi_g
  have hsf : Mono sf := NatTrans.mono_of_mono_app sf
  have hsg : Epi sg := NatTrans.epi_of_epi_app sg
  exact ShortComplex.ShortExact.mk'
    (Limits.colim.exact_mapShortComplex hS hc₁ hc₂ hc₃ f g
      (fun j => hf j.as) (fun j => hg j.as))
    (Limits.colim.map_mono' sf hc₁ hc₂ f (fun j => hf j.as))
    (Limits.colim.map_epi' sg c₂ hc₃ g (fun j => hg j.as))

/-- In a short exact sequence of cochain complexes, the left complex is acyclic as soon as the
middle and the right one are: the long exact sequence of cohomology presents `Hʲ(X₁)` between
`Hʲ⁻¹(X₃)` and `Hʲ(X₂)`. -/
theorem acyclic_X₁_of_shortExact (T : ShortComplex (CochainComplex A ℤ)) (hT : T.ShortExact)
    (h₂ : T.X₂.Acyclic) (h₃ : T.X₃.Acyclic) : T.X₁.Acyclic := by
  intro j
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hT.homology_exact₁ (j - 1) j (by simp)).isZero_X₂
    ((h₃ (j - 1)).isZero_homology.eq_of_src _ _) ((h₂ j).isZero_homology.eq_of_tgt _ _)

/-- In a short exact sequence of cochain complexes, the right complex is acyclic as soon as the
left and the middle one are: the long exact sequence of cohomology presents `Hⁱ(X₃)` between
`Hⁱ(X₂)` and `Hⁱ⁺¹(X₁)`. -/
theorem acyclic_X₃_of_shortExact (T : ShortComplex (CochainComplex A ℤ)) (hT : T.ShortExact)
    (h₁ : T.X₁.Acyclic) (h₂ : T.X₂.Acyclic) : T.X₃.Acyclic := by
  intro i
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hT.homology_exact₃ i (i + 1) (by simp)).isZero_X₂
    ((h₂ i).isZero_homology.eq_of_src _ _) ((h₁ (i + 1)).isZero_homology.eq_of_tgt _ _)

end Abelian

/-! ### Tensoring a short exact sequence of complexes on a ringed site -/

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (R : Sheaf J CommRingCat.{w})
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} R).Additive]
  [∀ M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} R).obj M).Additive]
  [∀ K₁ K₂ : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ,
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

omit [∀ K₁ K₂ : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ,
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)] in
/-- **Stacks 03EX, sheaf case, with the flat sheaf as the second tensor factor.**  Tensoring a
short exact sequence of sheaves of modules whose third term is flat with a fixed sheaf of
modules `G` on the *left* keeps it short exact.  This is
`Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj`, which tensors with
  `G` on the right, carried
across the braiding `Stacks.SheafOfModules.Tensor.sheafTensorBraiding` of the tensor product. -/
theorem shortExact_map_sheafTensor_obj
    (Q : ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))) (hQ :
      Q.ShortExact)
    (hflat : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) Q.X₃)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :
    (Q.map ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj G)).ShortExact :=
  (ShortComplex.shortExact_iff_of_iso (Q.mapNatIso
    ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding R).app G))).2
    (Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj R Q hQ hflat G)

/-- `Tot(F ⊗ -)` is additive, by the general additivity of
`Functor.map₂HomologicalComplex` in its second variable. -/
instance additive_tensorComplex_obj
    (F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj F).Additive :=
  Stacks.SheafOfModules.Tensor.Reduction.map₂HomologicalComplex_obj_additive
    (Stacks.SheafOfModules.Tensor.sheafTensor R) F

/-- The summand of `Tot(F ⊗ -)` applied to a morphism: on the summand indexed by `p + q = n`,
the map `Tot(F ⊗ φ)` in degree `n` is `F^p ⊗ φ^q`.  This is Mathlib's
`HomologicalComplex.ι_mapBifunctorMap`, read through the definition of
`Stacks.SheafOfModules.Tensor.tensorComplex` and with the identity on the left factor contracted
  away; it is
recorded separately, in one spelling, because a rewrite cannot unfold `tensorComplex`. -/
theorem ι_comp_tensorComplex_map
    (F K L : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ) (φ :
      K ⟶ L)
    (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιMapBifunctor F K (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)
          p q n h ≫ (((Stacks.SheafOfModules.Tensor.tensorComplex R).obj F).map φ).f n =
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (F.X p)).map (φ.f q) ≫
        HomologicalComplex.ιMapBifunctor F L (Stacks.SheafOfModules.Tensor.sheafTensor R)
          (ComplexShape.up ℤ) p q n h := by
  refine (HomologicalComplex.ι_mapBifunctorMap (f₁ := 𝟙 F) (f₂ := φ)
    (F := Stacks.SheafOfModules.Tensor.sheafTensor R) (c := ComplexShape.up ℤ) p q n h).trans ?_
  simp

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} R).Additive]
  [∀ M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} R).obj M).Additive]
  [∀ K₁ K₂ : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ,
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)] in
/-- **Direct sums of sheaves of modules indexed by a type in `Type 0` are exact.**  Filtered
colimits of sheaves of modules are exact (Tag 03DB) and AB5 implies AB4; the resulting AB4 at
the module universe is then shrunk to `Type 0`, which is where the antidiagonal index of a
total complex lives.

`Stacks.SheafOfModules.FlatCoproduct.hasExactColimitsOfShape_discrete` is the same fact for an
index type *in* the module universe, but it needs the module universe to contain the object
universe of the site.  Restricting to shapes in `Type 0` — all the total complex consumes —
removes that condition and so leaves the two site universes free of the module universe. -/
lemma hasExactColimitsOfShape_discrete_ofSize (β : Type) :
    HasExactColimitsOfShape (Discrete β)
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) := by
  let _ : AB5OfSize.{w, w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules _
  let _ : HasFiniteBiproducts (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let _ : AB4OfSize.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    AB4.of_AB5 _
  let _ : AB4OfSize.{0} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) :=
    AB4OfSize_shrink _
  exact AB4OfSize.ofShape β

/-- **Tensoring a short exact sequence of complexes with flat third term by a fixed complex
keeps it short exact.**  In total degree `n` both sides are coproducts over `p + q = n`: the
summand `F^p ⊗ -` of the sequence of `q`-th terms is short exact by Tag 03EX and the flatness
of `K₃^q` (`shortExact_map_sheafTensor_obj`), and a coproduct of short exact sequences is
short exact because `Mod(O)` satisfies AB4 (`shortExact_coproduct`). -/
@[sga "4 XVII 4.1.1" "(ii), special case"]
theorem shortExact_tensorComplex
    (F : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (S : ShortComplex (CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf
      R)) ℤ))
    (hS : S.ShortExact)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) (S.X₃.X i)) :
    (S.map ((Stacks.SheafOfModules.Tensor.tensorComplex R).obj F)).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  let T := (Stacks.SheafOfModules.Tensor.tensorComplex R).obj F
  let β : Type := {pq : ℤ × ℤ // pq.1 + pq.2 = n}
  let U : β → ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) := fun b
    =>
    (S.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) b.val.2)).map
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (F.X b.val.1))
  have := hasExactColimitsOfShape_discrete_ofSize R β
  have hU : ∀ b, (U b).ShortExact := fun b =>
    shortExact_map_sheafTensor_obj R _
      (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) b.val.2))
      (hflat b.val.2) (F.X b.val.1)
  let π := ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  let cofan : ∀ K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    ℤ,
      Cofan fun b : β => ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (F.X b.val.1)).obj (K.X
        b.val.2) :=
    fun K => Cofan.mk ((T.obj K).X n) fun b =>
      HomologicalComplex.ιMapBifunctor F K (Stacks.SheafOfModules.Tensor.sheafTensor R)
        (ComplexShape.up ℤ)
        b.val.1 b.val.2 n b.property
  have hcofan : ∀ K, IsColimit (cofan K) := fun K =>
    (((Stacks.SheafOfModules.Tensor.sheafTensor R).mapBifunctorHomologicalComplex (ComplexShape.up
      ℤ)
      (ComplexShape.up ℤ)).obj F).obj K |>.toGradedObject.isColimitCofanMapObj π n
  refine shortExact_coproduct U hU (c₁ := cofan S.X₁) (hcofan S.X₁) (c₂ := cofan S.X₂)
    (hcofan S.X₂) (c₃ := cofan S.X₃) (hcofan S.X₃) ((T.map S.f).f n) ((T.map S.g).f n)
    (by simpa using congrArg (fun φ => φ.f n) (S.map ((Stacks.SheafOfModules.Tensor.tensorComplex
      R).obj F)).zero)
    (fun b => ?_) (fun b => ?_)
  · exact ι_comp_tensorComplex_map R F S.X₁ S.X₂ S.f b.val.1 b.val.2 n b.property
  · exact ι_comp_tensorComplex_map R F S.X₂ S.X₃ S.g b.val.1 b.val.2 n b.property

/-! ### The three implications -/

variable (S : ShortComplex
  (CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ))

/-- **Stacks 0G7B, left complex.**  In a short exact sequence of complexes of `O`-modules whose
right complex has flat terms, K-flatness of the middle and of the right complex implies
K-flatness of the left complex. -/
@[stacks 0G7B "left complex"]
theorem kFlat_left_of_shortExact (hS : S.ShortExact)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) (S.X₃.X i))
    (h₂ : Stacks.SheafOfModules.KFlat.KFlat R S.X₂) (h₃ : Stacks.SheafOfModules.KFlat.KFlat R S.X₃)
      :
    Stacks.SheafOfModules.KFlat.KFlat R S.X₁ := fun F hF =>
  acyclic_X₁_of_shortExact _ (shortExact_tensorComplex R F S hS hflat) (h₂ F hF) (h₃ F hF)

/-- **Stacks 0G7B, middle complex.**  In a short exact sequence of complexes of `O`-modules
whose right complex has flat terms, K-flatness of the two outer complexes implies K-flatness of
the middle complex. -/
@[stacks 0G7B "middle complex"]
theorem kFlat_middle_of_shortExact (hS : S.ShortExact)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) (S.X₃.X i))
    (h₁ : Stacks.SheafOfModules.KFlat.KFlat R S.X₁) (h₃ : Stacks.SheafOfModules.KFlat.KFlat R S.X₃)
      :
    Stacks.SheafOfModules.KFlat.KFlat R S.X₂ := fun F hF =>
  (shortExact_tensorComplex R F S hS hflat).acyclic_X₂ (h₁ F hF) (h₃ F hF)

/-- **Stacks 0G7B, right complex.**  In a short exact sequence of complexes of `O`-modules whose
right complex has flat terms, K-flatness of the left and of the middle complex implies
K-flatness of the right complex. -/
@[stacks 0G7B "right complex"]
theorem kFlat_right_of_shortExact (hS : S.ShortExact)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := R) (S.X₃.X i))
    (h₁ : Stacks.SheafOfModules.KFlat.KFlat R S.X₁) (h₂ : Stacks.SheafOfModules.KFlat.KFlat R S.X₂)
      :
    Stacks.SheafOfModules.KFlat.KFlat R S.X₃ := fun F hF =>
  acyclic_X₃_of_shortExact _ (shortExact_tensorComplex R F S hS hflat) (h₁ F hF) (h₂ F hF)

end Stacks.SheafOfModules.KFlatTwoOutOfThree

end
