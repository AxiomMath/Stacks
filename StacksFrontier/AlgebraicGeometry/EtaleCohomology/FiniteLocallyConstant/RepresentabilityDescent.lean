module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCoveringFpqc
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityChartTransport
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityLargeIndex
public import StacksFrontier.AlgebraicGeometry.Descent.FiniteFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteConstantRepresentable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.CoverCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.OverMapConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SheafRepresentability.Subcanonical
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.FiniteEtaleCovers
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A finite locally constant sheaf of sets is representable by a finite étale scheme

Let `B` be a big étale site and `X` an object of it. A finite locally constant sheaf of sets on
the small étale site of `X` is represented by an object of that site whose structure morphism is
finite, that is, by a scheme finite étale over `X`. Together with the converse
`Stacks.EtaleCohomology.isFiniteLocallyConstant_of_finiteEtaleRepresentable` this is Stacks
59.64.4 (Tag 03RV), and here it is **unconditional**: the effective descent it needs is Stacks
0245, which this library proves as
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex`.

## Main results

* `Stacks.EtaleCohomology.exists_sliceRepresentatives_of_isFiniteLocallyConstant` — a finite
  locally constant sheaf has a covering of `X` on each member of which it is represented, in the
  localized site, by an object of the slice with finite étale structure morphism.
* `Stacks.EtaleCohomology.isFiniteLocallyConstant_iff_finiteEtaleRepresentable` — **Tag 03RV**,
  with no hypothesis.

## Implementation notes

**The shape of the local data.** Finite local constancy trivializes the sheaf on the *localized*
sites `C/V i`, so the local representing objects are produced as objects of the slice
`Over (V i)` rather than of the small étale site of the scheme underlying `V i`. The passage from
the constant sheaf to a representable one on a slice is assembled from three results already in
the library: `Stacks.ConstantSheaf.overPullbackConstantSheafIsoType` identifies the constant
sheaf on a slice with the restriction of the constant sheaf, `Stacks.EtaleCohomology.splitObj`
represents the finite constant sheaf on the site itself, and
`Stacks.EtaleCohomology.overUliftYonedaIso` says that the restriction of a representable sheaf
to a slice is represented by the product with the slicing object. No new geometry enters.

**The transition isomorphisms are not chosen, they are computed.** Over a product `A i × V j` of
two members of the covering the sheaf has a canonical section — the image of the identity under
the trivialization — and the local representatives are *characterized* by their sections, which
is `Stacks.EtaleCohomology.localSection_hom_ext`. The transition
`Stacks.EtaleCohomology.localTransitionIso` is therefore defined outright, and the cocycle
condition is an equality of maps into a representing object, hence an equality of sections. This
is why no coherence has to be hypothesised anywhere below.

**From a descent datum of the slices to one of schemes.** The slice `Over (V i)` of the small
étale site is carried into `Over X` by
`H = SmallEtale.inclusion ⋙ Over.post B.inclusion`, which preserves binary products
(`Stacks.EtaleCohomology.smallEtaleInclusion_preservesBinaryProducts`): the small étale site has
a terminal object, namely `X` itself, and `H` preserves pullbacks because
`AlgebraicGeometry.SmallEtale.toScheme` does and `Over.forget X` reflects them. Products of the
slices are therefore carried to fibre products of schemes, and the transitions above become the
gluing isomorphisms of a descent datum relative to the covering family, which
`AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex` makes effective — a
finite morphism being affine. Finiteness and étaleness of the descended morphism follow because
both properties are local at the target for the fpqc topology.

**Recovering the sheaf.** Effectivity produces the representing object, not yet an isomorphism of
sheaves. The chart of the descent datum gives a projection of each local representative to it,
compatibly with the transitions, and therefore an isomorphism of the restrictions of the two
sheaves over each member of the covering. Those isomorphisms agree on overlaps — again because a
map into a representable is determined by a section — so they glue, by
`Stacks.EtaleCohomology.sheafIsoOfCompatibleLocalIsos`, which is the sheaf condition for the
internal hom.

## References

* [Stacks Project, Tag 03RV](https://stacks.math.columbia.edu/tag/03RV)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 02W5](https://stacks.math.columbia.edu/tag/02W5)
* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Stacks.EtaleCohomology

/-! ### Restriction of representable sheaves and presheaves -/

section Generic

/-- Restricting the presheaf represented by `G.obj U` along a fully faithful `G` gives the
presheaf represented by `U`. -/
public noncomputable def restrictedUliftYonedaIso
    {C : Type (u + 1)} {D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    (G : C ⥤ D) [G.Full] [G.Faithful] (U : C) :
    G.op ⋙ uliftYoneda.{u + 1}.obj (G.obj U) ≅ uliftYoneda.{u + 1}.obj U :=
  NatIso.ofComponents
    (fun V ↦ ((Equiv.ulift.trans
      ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm.trans
        Equiv.ulift.symm))).toIso)
    (fun f ↦ by
      ext x
      apply ULift.ext
      apply G.map_injective
      simp [Equiv.ulift])

/-- Restricting the presheaf represented by `U` along the left adjoint of an adjoint pair gives
the presheaf represented by the right adjoint's value at `U`. -/
public noncomputable def adjunctionUliftYonedaIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (U : D) :
    L.op ⋙ uliftYoneda.{u + 1}.obj U ≅ uliftYoneda.{u + 1}.obj (R.obj U) :=
  NatIso.ofComponents (fun W ↦
    (Equiv.ulift.trans ((adj.homEquiv W.unop U).trans Equiv.ulift.symm)).toIso)
    (fun f ↦ by
      ext g
      apply ULift.ext
      exact adj.homEquiv_naturality_left f.unop g.down)

/-- **Morphisms over `U` into a product projection.** A morphism over `U` from `Z` to the first
projection `U × V ⟶ U` is the same thing as a morphism `Z.left ⟶ V`. -/
public noncomputable def overProdHomEquiv {C : Type*} [Category* C] [HasBinaryProducts C]
    (U V : C) (Z : Over U) :
    (Z ⟶ Over.mk (prod.fst : U ⨯ V ⟶ U)) ≃ (Z.left ⟶ V) where
  toFun g := g.left ≫ prod.snd
  invFun h := Over.homMk (prod.lift Z.hom h) (by simp)
  left_inv g := by
    ext
    apply prod.hom_ext
    · simpa using (Over.w g).symm
    · simp
  right_inv h := by simp

/-- `Stacks.EtaleCohomology.overProdHomEquiv` is natural in `Z`. -/
public lemma overProdHomEquiv_naturality {C : Type*} [Category* C] [HasBinaryProducts C]
    (U V : C) {Z Z' : Over U} (f : Z' ⟶ Z) (h : Z.left ⟶ V) :
    (overProdHomEquiv U V Z').symm (f.left ≫ h) = f ≫ (overProdHomEquiv U V Z).symm h := by
  ext
  apply prod.hom_ext
  · simp [overProdHomEquiv]
  · simp [overProdHomEquiv]

/-- **The restriction of a representable sheaf to a slice is representable.** On a subcanonical
site the restriction of the sheaf represented by `V` to the localized site at `U` is represented
by the first projection of the product `U × V`. -/
public noncomputable def overUliftYonedaIso
    {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C]
    (J : GrothendieckTopology C) [J.Subcanonical] (U V : C) :
    (J.uliftYoneda.{u + 1}.obj V).over U ≅
      (J.over U).uliftYoneda.{u + 1}.obj (Over.mk (prod.fst : U ⨯ V ⟶ U)) := by
  apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
  refine NatIso.ofComponents (fun W ↦
    (Equiv.ulift.trans ((overProdHomEquiv U V W.unop).symm.trans Equiv.ulift.symm)).toIso) ?_
  intro W Z f
  ext g
  apply ULift.ext
  exact overProdHomEquiv_naturality U V f.unop g.down

/-- On a subcanonical site the sheafified Yoneda embedding agrees with Mathlib's Yoneda embedding
into sheaves. -/
public noncomputable def sheafifiedYonedaIsoUliftYoneda
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [J.Subcanonical] [HasWeakSheafify J (Type (u + 1))] (U : C) :
    (Sheaf.sheafifiedYoneda J).obj U ≅ J.uliftYoneda.{u + 1}.obj U :=
  (Sheaf.uliftYonedaIsoSheafifiedYoneda J).app U |>.symm

/-- Pulling the sheaf represented by `A` back along a morphism of a subcanonical site gives the
sheaf represented by the base change of `A`. -/
public noncomputable def overMapUliftYonedaIso
    {C : Type (u + 1)} [Category.{u} C] [HasPullbacks C]
    (J : GrothendieckTopology C) [J.Subcanonical]
    {V W : C} (f : W ⟶ V) (A : Over V) :
    (J.overMapPullback (Type (u + 1)) f).obj ((J.over V).uliftYoneda.{u + 1}.obj A) ≅
      (J.over W).uliftYoneda.{u + 1}.obj ((Over.pullback f).obj A) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (adjunctionUliftYonedaIso (Over.mapPullbackAdj f) A)

/-- The slice of a slice, read as a slice of the underlying object: `C/V` is carried into
`Over (H.obj V).left` by `H`. -/
public abbrev overUnderlyingFunctor
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {S : D} (H : C ⥤ Over S) (V : C) : Over V ⥤ Over (H.obj V).left :=
  Over.post H ⋙ (Over.iteratedSliceEquiv (H.obj V)).functor

/-- Composing `Stacks.EtaleCohomology.overUnderlyingFunctor` with the forgetful functor of the
slice recovers `H`. -/
public noncomputable def overUnderlyingFunctorMapIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {S : D} (H : C ⥤ Over S) (V : C) :
    overUnderlyingFunctor H V ⋙ Over.map (H.obj V).hom ≅ Over.forget V ⋙ H :=
  NatIso.ofComponents (fun W ↦ Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (H.obj W.left).hom = (H.map W.hom).left ≫ (H.obj V).hom
    simpa only [Category.id_comp] using (Over.w (H.map W.hom)).symm)) (fun f ↦ by
      ext
      change (H.map f.left).left ≫ 𝟙 _ = 𝟙 _ ≫ (H.map f.left).left
      simp)

/-- The restriction to `C/V` of the presheaf represented by `U` is the presheaf represented, in
`Over (H.obj V).left`, by the base change of `H.obj U`. -/
public noncomputable def restrictionUliftYonedaIsoPullback
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] [HasPullbacks D]
    {S : D} (H : C ⥤ Over S) [H.Full] [H.Faithful] (V U : C) :
    (Over.forget V).op ⋙ uliftYoneda.{u + 1}.obj U ≅
      (overUnderlyingFunctor H V).op ⋙
        uliftYoneda.{u + 1}.obj ((Over.pullback (H.obj V).hom).obj (H.obj U)) :=
  Functor.isoWhiskerLeft (Over.forget V).op (restrictedUliftYonedaIso H U).symm ≪≫
    Functor.isoWhiskerRight (NatIso.op (overUnderlyingFunctorMapIso H V))
      (uliftYoneda.{u + 1}.obj (H.obj U)) ≪≫
    Functor.isoWhiskerLeft (overUnderlyingFunctor H V).op
      (adjunctionUliftYonedaIso (Over.mapPullbackAdj (H.obj V).hom) (H.obj U))

end Generic

/-! ### Local sections of a representable sheaf -/

section LocalSections

variable {C : Type (u + 1)} [Category.{u} C]
  {J : GrothendieckTopology C} [J.Subcanonical]
  {F : Sheaf J (Type (u + 1))} {V : C} {A : Over V}
  (e : F.over V ≅ (J.over V).uliftYoneda.{u + 1}.obj A)

/-- **The tautological section.** The section of `F` over the representing object `A` which
corresponds to the identity of `A`. -/
public def localSection : F.obj.obj (Opposite.op A.left) :=
  e.inv.hom.app (Opposite.op A) ⟨𝟙 A⟩

/-- The morphism to `A` which a section of `F` over an object of `C/V` corresponds to. -/
public def localLift {W : C} (f : W ⟶ V) (s : F.obj.obj (Opposite.op W)) : W ⟶ A.left :=
  (e.hom.hom.app (Opposite.op (Over.mk f)) s).down.left

/-- The morphism attached to a section is a morphism over `V`. -/
public lemma localLift_hom {W : C} (f : W ⟶ V) (s : F.obj.obj (Opposite.op W)) :
    localLift e f s ≫ A.hom = f :=
  Over.w _

/-- Pulling the tautological section back along the morphism attached to a section recovers that
section. -/
public lemma localSection_localLift {W : C} (f : W ⟶ V)
    (s : F.obj.obj (Opposite.op W)) :
    F.obj.map (localLift e f s).op (localSection e) = s := by
  let g : Over.mk f ⟶ A := (e.hom.hom.app (Opposite.op (Over.mk f)) s).down
  have h := ConcreteCategory.congr_hom (e.inv.hom.naturality g.op)
    (show ULift.{u + 1} (A ⟶ A) from ⟨𝟙 A⟩)
  change e.inv.hom.app (Opposite.op (Over.mk f)) ⟨g ≫ 𝟙 A⟩ =
    F.obj.map g.left.op (localSection e) at h
  rw [Category.comp_id] at h
  show F.obj.map g.left.op (localSection e) = s
  rw [← h]
  exact congrArg (fun t : F.over V ⟶ F.over V ↦
    t.hom.app (Opposite.op (Over.mk f)) s) e.hom_inv_id

/-- The morphism attached to the pullback of the tautological section along `g` is `g`. -/
public lemma localLift_localSection {W : C} (g : W ⟶ A.left) :
    localLift e (g ≫ A.hom) (F.obj.map g.op (localSection e)) = g := by
  let g' : Over.mk (g ≫ A.hom) ⟶ A := Over.homMk g
  have h := NatTrans.naturality_apply e.hom.hom g'.op (localSection e)
  change e.hom.hom.app (Opposite.op (Over.mk (g ≫ A.hom)))
    (F.obj.map g.op (localSection e)) = _ at h
  have hi : e.hom.hom.app (Opposite.op A) (localSection e) = ⟨𝟙 A⟩ :=
    ConcreteCategory.congr_hom (congrArg (fun t ↦ t.hom.app (Opposite.op A)) e.inv_hom_id) _
  rw [hi] at h
  change _ = (ULift.up (g' ≫ 𝟙 A)) at h
  simpa [localLift, g'] using congrArg (fun x ↦ x.down.left) h

/-- **A morphism to a representing object is determined by its section.** Two morphisms to `A`
which agree over `V` and pull the tautological section back to the same section are equal. -/
public lemma localSection_hom_ext {W : C} {g h : W ⟶ A.left}
    (hbase : g ≫ A.hom = h ≫ A.hom)
    (hsection : F.obj.map g.op (localSection e) = F.obj.map h.op (localSection e)) : g = h := by
  rw [← localLift_localSection e g, ← localLift_localSection e h, hbase, hsection]

end LocalSections

/-! ### The transition isomorphisms of a family of local representatives -/

section Transitions

variable {C : Type (u + 1)} [Category.{u} C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} [J.Subcanonical]
  {F : Sheaf J (Type (u + 1))}
  {V₁ V₂ V₃ : C} {A₁ : Over V₁} {A₂ : Over V₂} {A₃ : Over V₃}
  (e₁ : F.over V₁ ≅ (J.over V₁).uliftYoneda.{u + 1}.obj A₁)
  (e₂ : F.over V₂ ≅ (J.over V₂).uliftYoneda.{u + 1}.obj A₂)
  (e₃ : F.over V₃ ≅ (J.over V₃).uliftYoneda.{u + 1}.obj A₃)

/-- **The transition between two local representatives.** Over `A₁ × V₂` the sheaf `F` has the
section pulled back from the tautological one of `A₁`, and the second trivialization turns it
into a morphism to `A₂`. -/
public noncomputable def localTransition : A₁.left ⨯ V₂ ⟶ V₁ ⨯ A₂.left :=
  prod.lift (prod.fst ≫ A₁.hom)
    (localLift e₂ prod.snd (F.obj.map prod.fst.op (localSection e₁)))

/-- The transition preserves the first component of the base. -/
public lemma localTransition_fst :
    localTransition e₁ e₂ ≫ prod.fst = prod.fst ≫ A₁.hom := by
  simp [localTransition]

/-- The transition preserves the second component of the base. -/
public lemma localTransition_base :
    localTransition e₁ e₂ ≫ prod.snd ≫ A₂.hom = prod.snd := by
  simp [localTransition, localLift_hom]

/-- The transition matches the two tautological sections. -/
public lemma localTransition_section :
    F.obj.map (localTransition e₁ e₂ ≫ prod.snd).op (localSection e₂) =
      F.obj.map prod.fst.op (localSection e₁) := by
  simp only [localTransition, prod.lift_snd, localSection_localLift]

/-- `Stacks.EtaleCohomology.localTransition_section` with the composition on the sections side. -/
public lemma localTransition_section_apply :
    F.obj.map (localTransition e₁ e₂).op (F.obj.map prod.snd.op (localSection e₂)) =
      F.obj.map prod.fst.op (localSection e₁) := by
  simpa only [op_comp, Functor.map_comp, types_comp_apply] using localTransition_section e₁ e₂

/-- `Stacks.EtaleCohomology.localTransition_section` after precomposition. -/
public lemma localTransition_section_precomp {W : C} (g : W ⟶ A₁.left ⨯ V₂) :
    F.obj.map (g ≫ localTransition e₁ e₂ ≫ prod.snd).op (localSection e₂) =
      F.obj.map (g ≫ prod.fst).op (localSection e₁) := by
  rw [op_comp, Functor.map_comp, types_comp_apply, localTransition_section]
  rw [op_comp, Functor.map_comp, types_comp_apply]

attribute [local simp] localTransition_fst localTransition_base localTransition_section

/-- The transition in one direction is inverse to the transition in the other. -/
public lemma localTransition_inverse :
    localTransition e₁ e₂ ≫ (prod.braiding _ _).hom ≫
      localTransition e₂ e₁ ≫ (prod.braiding _ _).hom = 𝟙 _ := by
  apply prod.hom_ext
  · apply localSection_hom_ext e₁
    · simp
    · simp only [Category.assoc, prod.braiding_hom, prod.lift_fst, Category.id_comp]
      simp only [op_comp, Functor.map_comp, types_comp_apply, localTransition_section_apply]
      simp only [← Functor.map_comp_apply, ← op_comp, prod.lift_fst, localTransition_section]
  · simp

/-- **The transition is an isomorphism.** -/
public noncomputable def localTransitionIso : A₁.left ⨯ V₂ ≅ V₁ ⨯ A₂.left where
  hom := localTransition e₁ e₂
  inv := (prod.braiding _ _).hom ≫ localTransition e₂ e₁ ≫ (prod.braiding _ _).hom
  hom_inv_id := localTransition_inverse e₁ e₂
  inv_hom_id := by
    have h := localTransition_inverse e₂ e₁
    apply (cancel_epi (prod.braiding A₂.left V₁).hom).mp
    apply (cancel_mono (prod.braiding V₁ A₂.left).hom).mp
    simpa only [Category.assoc, prod.symmetry_assoc, prod.symmetry, Category.id_comp,
      Category.comp_id] using h

/-- **The cocycle condition**, which holds automatically: both sides are morphisms to a
representing object with the same section. -/
public lemma localTransition_cocycle :
    prod.map (localTransition e₁ e₂) (𝟙 V₃) ≫
      prodMapLastTwo (localTransition e₂ e₃) =
        prodMapFirstThird (localTransition e₁ e₃) := by
  apply prod.hom_ext
  · apply prod.hom_ext <;> simp [prodMapLastTwo, prodMapFirstThird]
  · apply localSection_hom_ext e₃
    · simp [prodMapLastTwo, prodMapFirstThird]
    · simp only [prodMapLastTwo, prodMapFirstThird, Category.assoc, prod.associator_inv,
        prod.associator_hom, prod.braiding_hom, prod.lift_snd_assoc, prod.lift_fst_assoc,
        prod.lift_snd, prod.lift_fst, prod.map_snd_assoc, prod.map_fst_assoc]
      simp only [op_comp, Functor.map_comp, types_comp_apply, localTransition_section_apply]
      simp only [← Functor.map_comp_apply, ← op_comp, prod.map_fst_assoc, prod.map_fst,
        prod.lift_fst_assoc, prod.lift_fst]
      simp only [op_comp, Functor.map_comp, types_comp_apply, localTransition_section_apply]
      simp

end Transitions

/-! ### Transporting products along a functor -/

section ProductTransport

variable {C D : Type*} [Category* C] [Category* D]
  [HasBinaryProducts C] [HasBinaryProducts D]
  (H : C ⥤ D)

/-- The comparison map of a left-associated triple product. -/
public noncomputable def tripleComparison (A B C' : C) :
    H.obj ((A ⨯ B) ⨯ C') ⟶ (H.obj A ⨯ H.obj B) ⨯ H.obj C' :=
  prodComparison H (A ⨯ B) C' ≫ prod.map (prodComparison H A B) (𝟙 _)

@[local simp]
private lemma prodComparison_simps (A B : C) :
    (prodComparison H A B ≫ prod.fst = H.map prod.fst) ∧
      (prodComparison H A B ≫ prod.snd = H.map prod.snd) :=
  ⟨prodComparison_fst H A B, prodComparison_snd H A B⟩

/-- The first projection of the triple comparison. -/
public lemma tripleComparison_fst_fst (A B C' : C) :
    tripleComparison H A B C' ≫ prod.fst ≫ prod.fst = H.map (prod.fst ≫ prod.fst) := by
  simp only [tripleComparison, Category.assoc, prod.map_fst_assoc, prodComparison_fst_assoc,
    prodComparison_fst, ← H.map_comp]

/-- The second projection of the triple comparison. -/
public lemma tripleComparison_fst_snd (A B C' : C) :
    tripleComparison H A B C' ≫ prod.fst ≫ prod.snd = H.map (prod.fst ≫ prod.snd) := by
  simp only [tripleComparison, Category.assoc, prod.map_fst_assoc, prodComparison_fst_assoc,
    prodComparison_snd, ← H.map_comp]

/-- The third projection of the triple comparison. -/
public lemma tripleComparison_snd (A B C' : C) :
    tripleComparison H A B C' ≫ prod.snd = H.map prod.snd := by
  simp [tripleComparison]

/-- The comparison map is compatible with lifts. -/
public lemma prodComparison_lift {A B T : C} (f : T ⟶ A) (g : T ⟶ B) :
    H.map (prod.lift f g) ≫ prodComparison H A B = prod.lift (H.map f) (H.map g) := by
  apply prod.hom_ext <;>
    simp only [Category.assoc, prodComparison_fst, prodComparison_snd, ← H.map_comp,
      prod.lift_fst, prod.lift_snd]

/-- A map of the first two factors of a triple product is transported by the triple
comparison. -/
public lemma tripleComparison_first
    {A B C' A' B' : C} (g : A ⨯ B ⟶ A' ⨯ B')
    (h : H.obj A ⨯ H.obj B ⟶ H.obj A' ⨯ H.obj B')
    (hh : prodComparison H A B ≫ h = H.map g ≫ prodComparison H A' B') :
    tripleComparison H A B C' ≫ prod.map h (𝟙 _) =
      H.map (prod.map g (𝟙 C')) ≫ tripleComparison H A' B' C' := by
  simp only [tripleComparison, Category.assoc, ← prod.map_comp_id, hh]
  rw [prod.map_comp_id]
  simp only [prodComparison_natural_assoc, H.map_id]

/-- A map of the last two factors of a triple product is transported by the triple
comparison. -/
public lemma tripleComparison_last
    {A B C' B' C'' : C} (g : B ⨯ C' ⟶ B' ⨯ C'')
    (h : H.obj B ⨯ H.obj C' ⟶ H.obj B' ⨯ H.obj C'')
    (hh : prodComparison H B C' ≫ h = H.map g ≫ prodComparison H B' C'') :
    tripleComparison H A B C' ≫ prodMapLastTwo h =
      H.map (prodMapLastTwo g) ≫ tripleComparison H A B' C'' := by
  have hp : tripleComparison H A B C' ≫ prod.lift (prod.fst ≫ prod.snd) prod.snd =
      H.map (prod.lift (prod.fst ≫ prod.snd) prod.snd) ≫ prodComparison H B C' := by
    apply prod.hom_ext <;>
      simp only [tripleComparison, Category.assoc, prod.map_fst_assoc, prod.map_snd,
        Category.comp_id, prodComparison_fst_assoc, prodComparison_fst, prodComparison_snd,
        ← H.map_comp, prod.lift_fst, prod.lift_snd]
  apply prod.hom_ext
  · apply prod.hom_ext
    · simp only [prodMapLastTwo, tripleComparison, Category.assoc, prod.associator_hom,
        prod.associator_inv, prod.map_fst_assoc, prod.lift_fst_assoc, prod.lift_fst,
        prodComparison_fst_assoc, prodComparison_fst, ← H.map_comp, prod.map_fst, Category.comp_id]
    · simp only [prodMapLastTwo, Category.assoc, prod.associator_inv,
        prod.lift_fst_assoc, prod.lift_snd, prod.map_snd_assoc, prod.associator_hom,
        prod.lift_snd_assoc]
      rw [← Category.assoc, hp]
      simp only [Category.assoc, reassoc_of% hh, prodComparison_fst]
      simp only [tripleComparison, Category.assoc, prod.map_fst_assoc, prod.map_snd_assoc,
        prodComparison_fst_assoc, prodComparison_snd, ← H.map_comp, prod.lift_fst_assoc,
        prod.lift_snd_assoc, prod.lift_snd]
  · simp only [prodMapLastTwo, Category.assoc, prod.associator_inv,
      prod.lift_snd, prod.map_snd_assoc, prod.associator_hom, prod.lift_snd_assoc]
    rw [← Category.assoc, hp]
    simp only [Category.assoc, reassoc_of% hh, prodComparison_snd]
    simp only [tripleComparison, Category.assoc, prod.map_snd_assoc, prod.map_snd, Category.comp_id,
      prodComparison_snd, ← H.map_comp, prod.lift_snd_assoc, prod.lift_snd]

end ProductTransport

section ProductTransportFurther

variable {C D : Type*} [Category* C] [Category* D]
  [HasBinaryProducts C] [HasBinaryProducts D] (H : C ⥤ D)

/-- A map of the first and third factors of a triple product is transported by the triple
comparison. -/
public lemma tripleComparison_firstThird
    {A B C' A' C'' : C} (g : A ⨯ C' ⟶ A' ⨯ C'')
    (h : H.obj A ⨯ H.obj C' ⟶ H.obj A' ⨯ H.obj C'')
    (hh : prodComparison H A C' ≫ h = H.map g ≫ prodComparison H A' C'') :
    tripleComparison H A B C' ≫ prodMapFirstThird h =
      H.map (prodMapFirstThird g) ≫ tripleComparison H A' B C'' := by
  simp only [prodMapFirstThird, prodMapLastTwo, Category.assoc]
  rw [reassoc_of% tripleComparison_last H (prod.braiding B C').hom
    (prod.braiding (H.obj B) (H.obj C')).hom
    (map_braiding_hom_comp_prodComparison H).symm]
  rw [reassoc_of% tripleComparison_first H g h hh]
  rw [tripleComparison_last H (prod.braiding C'' B).hom
    (prod.braiding (H.obj C'') (H.obj B)).hom
    (map_braiding_hom_comp_prodComparison H).symm]
  simp only [H.map_comp, Category.assoc]

variable [PreservesLimitsOfShape (Discrete WalkingPair) H]

/-- An isomorphism of binary products is carried by a product-preserving functor to one of the
products of the images. -/
public noncomputable def mapProductIso {A B A' B' : C} (e : A ⨯ B ≅ A' ⨯ B') :
    H.obj A ⨯ H.obj B ≅ H.obj A' ⨯ H.obj B' :=
  (asIso (prodComparison H A B)).symm ≪≫ H.mapIso e ≪≫
    asIso (prodComparison H A' B')

omit [HasBinaryProducts D] in
/-- `Stacks.EtaleCohomology.mapProductIso` is compatible with the comparison maps. -/
public lemma prodComparison_mapProductIso {A B A' B' : C} (e : A ⨯ B ≅ A' ⨯ B') :
    prodComparison H A B ≫ (mapProductIso H e).hom =
      H.map e.hom ≫ prodComparison H A' B' := by
  simp [mapProductIso]

/-- A product-preserving functor carries a cocyclic family of transitions to one. -/
public lemma mapProductIso_cocycle {I : Type*} (V Y : I → C)
    (t : ∀ i j, Y i ⨯ V j ≅ V i ⨯ Y j)
    (ht : ∀ i j k, prod.map (t i j).hom (𝟙 (V k)) ≫
      prodMapLastTwo (t j k).hom = prodMapFirstThird (t i k).hom)
    (i j k : I) :
    prod.map (mapProductIso H (t i j)).hom (𝟙 (H.obj (V k))) ≫
      prodMapLastTwo (mapProductIso H (t j k)).hom =
        prodMapFirstThird (mapProductIso H (t i k)).hom := by
  have : IsIso (tripleComparison H (Y i) (V j) (V k)) := by
    dsimp [tripleComparison]
    infer_instance
  apply (cancel_epi (tripleComparison H (Y i) (V j) (V k))).mp
  rw [reassoc_of% tripleComparison_first H (t i j).hom _
    (prodComparison_mapProductIso H (t i j))]
  rw [tripleComparison_last H (t j k).hom _ (prodComparison_mapProductIso H (t j k))]
  rw [tripleComparison_firstThird H (t i k).hom _
    (prodComparison_mapProductIso H (t i k))]
  rw [← Category.assoc, ← H.map_comp, ht]

end ProductTransportFurther

section ChangeComponents

variable {C : Type*} [Category* C] [HasBinaryProducts C]
  {I : Type*} (V Y Y' : I → C) (c : ∀ i, Y' i ≅ Y i)
  (t : ∀ i j, Y i ⨯ V j ≅ V i ⨯ Y j)

/-- Transport a family of transitions along isomorphisms of their components. -/
public noncomputable def changeComponentTransition (i j : I) : Y' i ⨯ V j ≅ V i ⨯ Y' j :=
  prod.mapIso (c i) (Iso.refl _) ≪≫ t i j ≪≫
    prod.mapIso (Iso.refl _) (c j).symm

/-- Transporting a cocyclic family of transitions along isomorphisms of the components keeps it
cocyclic. -/
public lemma changeComponentTransition_cocycle
    (ht : ∀ i j k, prod.map (t i j).hom (𝟙 (V k)) ≫
      prodMapLastTwo (t j k).hom = prodMapFirstThird (t i k).hom)
    (i j k : I) :
    prod.map (changeComponentTransition V Y Y' c t i j).hom (𝟙 (V k)) ≫
      prodMapLastTwo (changeComponentTransition V Y Y' c t j k).hom =
        prodMapFirstThird (changeComponentTransition V Y Y' c t i k).hom := by
  have hc : prod.map (prod.map (𝟙 (V i)) (c j).inv) (𝟙 (V k)) ≫
      prod.lift (prod.fst ≫ prod.snd ≫ (c j).hom) prod.snd =
        prod.lift (prod.fst ≫ prod.snd) prod.snd := by
    apply prod.hom_ext <;> simp
  have hc' : prod.map (prod.map (c i).hom (𝟙 (V j))) (𝟙 (V k)) ≫
      prod.lift (prod.fst ≫ prod.fst) prod.snd =
        prod.lift (prod.fst ≫ prod.fst ≫ (c i).hom) prod.snd := by
    apply prod.hom_ext <;> simp
  have h := congrArg (fun g ↦ prod.map (prod.map (c i).hom (𝟙 (V j))) (𝟙 (V k)) ≫
    g ≫ prod.map (𝟙 (V i ⨯ V j)) (c k).inv) (ht i j k)
  convert h using 1 <;>
    simp [changeComponentTransition, prodMapLastTwo, prodMapFirstThird,
      prod.map_comp_id, prod.map_id_comp, prod.comp_lift, Category.assoc,
      reassoc_of% hc, reassoc_of% hc', -prod.map_map, -prod.map_map_assoc]

end ChangeComponents

/-! ### A descent datum from a cocyclic family of transitions -/

/-- An object over `V` is, after pushing forward along the structure morphism of `V`, the object
it was over the base. -/
public noncomputable def componentTotalIso {S W : Scheme.{u}} {g : W ⟶ S} {Y : Over S}
    (p : Y ⟶ Over.mk g) : (Over.map g).obj (Over.mk p.left) ≅ Y :=
  Over.isoMk (Iso.refl _) (by simpa using (Over.w p).symm)

/-- `Stacks.EtaleCohomology.componentTotalIso` carries the given morphism to the structure
morphism. -/
public lemma componentTotalIso_structure {S W : Scheme.{u}} {g : W ⟶ S} {Y : Over S}
    (p : Y ⟶ Over.mk g) :
    (componentTotalIso p).hom ≫ p = structureMap g (Over.mk p.left) := by
  ext
  simp [componentTotalIso]

/-- The inverse form of `Stacks.EtaleCohomology.componentTotalIso_structure`. -/
public lemma componentTotalIso_inv_structure {S W : Scheme.{u}} {g : W ⟶ S} {Y : Over S}
    (p : Y ⟶ Over.mk g) :
    (componentTotalIso p).inv ≫ structureMap g (Over.mk p.left) = p := by
  rw [← componentTotalIso_structure p, Iso.inv_hom_id_assoc]

/-- **A descent datum from transitions.** A family of schemes `Y i` over `S` with morphisms to
the members of a family `V i` of schemes over `S`, together with a cocyclic family of
isomorphisms `Y i × V j ≅ V i × Y j` compatible with those morphisms, is a descent datum
relative to the family. -/
public noncomputable def descentDataOfTransitions
    {S : Scheme.{u}} {I : Type v} (V : I → Scheme.{u}) (f : ∀ i, V i ⟶ S)
    (Y : I → Over S) (p : ∀ i, Y i ⟶ Over.mk (f i))
    (t : ∀ i j, Y i ⨯ Over.mk (f j) ≅ Over.mk (f i) ⨯ Y j)
    (hp : ∀ i j, (t i j).hom ≫ prod.map (𝟙 _) (p j) = prod.map (p i) (𝟙 _))
    (ht : ∀ i j k, prod.map (t i j).hom (𝟙 (Over.mk (f k))) ≫
      prodMapLastTwo (t j k).hom = prodMapFirstThird (t i k).hom) :
    DescentData (fun i ↦ f i) where
  obj i := Over.mk (p i).left
  gluing i j := Over.isoMk
    (changeComponentTransition (fun i ↦ Over.mk (f i)) Y _
      (fun i ↦ componentTotalIso (p i)) t i j) (by
      dsimp [changeComponentTransition]
      apply prod.hom_ext
      · simpa [Category.assoc, componentTotalIso_structure,
          componentTotalIso_inv_structure] using
          congrArg (fun g ↦ prod.map (componentTotalIso (p i)).hom (𝟙 (Over.mk (f j))) ≫
            g ≫ prod.fst) (hp i j)
      · simpa [Category.assoc, componentTotalIso_structure,
          componentTotalIso_inv_structure] using
          congrArg (fun g ↦ prod.map (componentTotalIso (p i)).hom (𝟙 (Over.mk (f j))) ≫
            g ≫ prod.snd) (hp i j))
  cocycle i j k := changeComponentTransition_cocycle (fun i ↦ Over.mk (f i)) Y _
    (fun i ↦ componentTotalIso (p i)) t ht i j k

/-! ### Gluing an isomorphism of sheaves -/

/-- **Compatible local isomorphisms glue.** A family of isomorphisms of the restrictions of two
sheaves to the members of a family covering the final object, agreeing on overlaps, comes from a
unique isomorphism of the sheaves: this is the sheaf condition for the internal hom. -/
public noncomputable def sheafIsoOfCompatibleLocalIsos
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    (F G : Sheaf J (Type v)) {I : Type*} (V : I → C)
    (hV : J.CoversTop V)
    (e : ∀ i, (Over.forget (V i)).op ⋙ F.obj ≅ (Over.forget (V i)).op ⋙ G.obj)
    (he : ∀ (Z : C) (i j : I) (f : Z ⟶ V i) (g : Z ⟶ V j),
      Functor.isoWhiskerLeft (Over.map f).op (e i) =
        Functor.isoWhiskerLeft (Over.map g).op (e j)) : F ≅ G := by
  let eh : Presheaf.FamilyOfElementsOnObjects (presheafHom F.obj G.obj) V :=
    fun i ↦ (e i).hom
  have hh : eh.IsCompatible := fun Z i j f g ↦ congrArg Iso.hom (he Z i j f g)
  let ei : Presheaf.FamilyOfElementsOnObjects (presheafHom G.obj F.obj) V :=
    fun i ↦ (e i).inv
  have hi : ei.IsCompatible := fun Z i j f g ↦ congrArg Iso.inv (he Z i j f g)
  let a := presheafHomSectionsEquiv F.obj G.obj (hh.section_ hV (G.property.hom F.obj))
  let b := presheafHomSectionsEquiv G.obj F.obj (hi.section_ hV (F.property.hom G.obj))
  have ha (i : I) : Functor.whiskerLeft (Over.forget (V i)).op a = (e i).hom := by
    have h := congrArg (fun s ↦ s.1 (Opposite.op (V i)))
      ((presheafHomSectionsEquiv F.obj G.obj).symm_apply_apply
        (hh.section_ hV (G.property.hom F.obj)))
    exact h.trans (hh.section_apply hV (G.property.hom F.obj) i)
  have hb (i : I) : Functor.whiskerLeft (Over.forget (V i)).op b = (e i).inv := by
    have h := congrArg (fun s ↦ s.1 (Opposite.op (V i)))
      ((presheafHomSectionsEquiv G.obj F.obj).symm_apply_apply
        (hi.section_ hV (F.property.hom G.obj)))
    exact h.trans (hi.section_apply hV (F.property.hom G.obj) i)
  refine { hom := ⟨a⟩, inv := ⟨b⟩, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply (sheafToPresheaf J (Type v)).map_injective
    apply (presheafHomSectionsEquiv F.obj F.obj).symm.injective
    apply hV.sections_ext ⟨_, F.property.hom F.obj⟩
    intro i
    change Functor.whiskerLeft (Over.forget (V i)).op (a ≫ b) =
      Functor.whiskerLeft (Over.forget (V i)).op (𝟙 F.obj)
    rw [Functor.whiskerLeft_comp, ha, hb, (e i).hom_inv_id]
    rfl
  · apply (sheafToPresheaf J (Type v)).map_injective
    apply (presheafHomSectionsEquiv G.obj G.obj).symm.injective
    apply hV.sections_ext ⟨_, G.property.hom G.obj⟩
    intro i
    change Functor.whiskerLeft (Over.forget (V i)).op (b ≫ a) =
      Functor.whiskerLeft (Over.forget (V i)).op (𝟙 G.obj)
    rw [Functor.whiskerLeft_comp, hb, ha, (e i).inv_hom_id]
    rfl

/-! ### Descending a datum of finite étale schemes -/

/-- **A scheme finite étale over `X` is an object of the small étale site of `X`.** -/
public theorem exists_smallSiteObject_of_finiteEtale
    (B : BigEtaleSite.{u}) (X : B.Scheme) (U : Over X.1)
    (hfinite : IsFinite U.hom) (hetale : Etale U.hom) :
    ∃ V : SmallEtale B X.1 X.2,
      IsFinite (B.inclusion.map V.obj.hom) ∧
        Nonempty (Over.mk (B.inclusion.map V.obj.hom) ≅ U) := by
  let Y : FiniteEtaleOver X.1 := MorphismProperty.Over.mk ⊤ U.hom ⟨hfinite, hetale⟩
  refine ⟨smallEtaleOfFiniteEtale (B := B) Y, ?_, ?_⟩
  · rw [smallEtaleOfFiniteEtale_hom]
    exact hfinite
  · refine ⟨Over.isoMk (Iso.refl U.left) ?_⟩
    rw [smallEtaleOfFiniteEtale_hom]
    show 𝟙 U.left ≫ U.hom = U.hom
    simp

/-- **A descent datum of finite étale schemes along an fpqc covering descends to one.** The
datum is effective by Stacks 0245, a finite morphism being affine, and both finiteness and
étaleness of the descended structure morphism are read off the members of the covering because
each property is local at the target for the fpqc topology. -/
@[sga "3 VIII 1.7.2" "(ii), special case", sga "3 X 4.2" "partial"]
public theorem exists_finiteEtale_of_descentData
    {S : Scheme.{u}} {I : Type v} {X : I → Scheme.{u}}
    (f : ∀ i, X i ⟶ S)
    (hfpqc : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData f)
    (hfinite : ∀ i, IsFinite (D.obj i).hom)
    (hetale : ∀ i, Etale (D.obj i).hom) :
    ∃ U : Over S,
      Nonempty ((canonicalFamilyDescentFunctor f).functor.obj U ≅ D) ∧
        IsFinite U.hom ∧ Etale U.hom := by
  classical
  have heffective : D.IsFamilyEffective :=
    DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex f hfpqc D (fun i ↦ by
      have := hfinite i
      infer_instance)
  obtain ⟨U, ⟨e⟩⟩ := heffective
  have key : ∀ (P : MorphismProperty Scheme.{u})
      [MorphismProperty.IsLocalAtTarget P Scheme.fpqcPrecoverage]
      [P.IsMultiplicative], (∀ i, P (D.obj i).hom) → P U.hom := by
    intro P _ _ hD
    apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd (P := P) hfpqc
    intro V g _ hmem
    obtain ⟨j⟩ := hmem
    have : IsIso (e.hom.hom j) :=
      (AlgebraicGeometry.DescentData.evaluation j).map_isIso e.hom
    have : IsIso (e.hom.hom j).left :=
      (Over.forget (X j)).map_isIso (e.hom.hom j)
    show P ((Over.pullback (f j)).obj U).hom
    rw [← (canonicalFamilyDescentFunctor f).obj U j, ← Over.w (e.hom.hom j)]
    exact P.comp_mem _ _ (P.of_isIso _) (hD j)
  refine ⟨U, ⟨e⟩, ?_, ?_⟩
  · have : MorphismProperty.IsLocalAtTarget
        (@IsFinite : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage :=
      Stacks.Morphisms.isFinite_isLocalAtTarget_fpqc
    exact key (@IsFinite) hfinite
  · exact key (@Etale) hetale

/-- **The small étale site embeds into schemes over `X` preserving binary products.** The site
has a terminal object, namely `X` itself, which the embedding carries to the terminal object of
`Over X`, and it preserves pullbacks because `AlgebraicGeometry.SmallEtale.toScheme` does and
`Over.forget X` reflects them. -/
public theorem smallEtaleToOver_preservesBinaryProducts
    (B : BigEtaleSite.{u}) (X : B.Scheme) :
    PreservesLimitsOfShape (Discrete WalkingPair) (smallEtaleToOver B X) := by
  let H := smallEtaleToOver B X
  have : PreservesLimitsOfShape WalkingCospan (H ⋙ Over.forget X.1) := by
    show PreservesLimitsOfShape WalkingCospan (SmallEtale.toScheme B X.1 X.2)
    infer_instance
  have : PreservesLimitsOfShape WalkingCospan H :=
    preservesLimitsOfShape_of_reflects_of_preserves H (Over.forget X.1)
  have : PreservesLimit (Functor.empty.{0} (SmallEtale B X.1 X.2)) H :=
    preservesTerminal_of_iso H <| H.mapIso (terminalIsTerminal.uniqueUpToIso
      (AlgebraicGeometry.SmallEtale.finalIsTerminal B X.1 X.2)) ≪≫
      (Over.mkIdTerminal (X := X.1)).uniqueUpToIso terminalIsTerminal
  have := preservesLimitsOfShape_pempty_of_preservesTerminal H
  exact preservesBinaryProducts_of_preservesTerminal_and_pullbacks H

/-! ### The local representatives, as objects of a slice -/

/-- **The product with a finite object of the small étale site is finite étale over the other
factor.** Its structure morphism is, after the product-preserving embedding into schemes over
`X`, the base change of the structure morphism of the finite factor. -/
public theorem isFinite_etale_left_map_prodFst
    (B : BigEtaleSite.{u}) (X : B.Scheme) (W U : SmallEtale B X.1 X.2)
    (hU : IsFinite (B.inclusion.map U.obj.hom)) :
    IsFinite ((smallEtaleToOver B X).map (prod.fst : W ⨯ U ⟶ W)).left ∧
      Etale ((smallEtaleToOver B X).map (prod.fst : W ⨯ U ⟶ W)).left := by
  have hH := smallEtaleToOver_preservesBinaryProducts B X
  let H := smallEtaleToOver B X
  have hcmp : IsIso (prodComparison H W U) := inferInstance
  have hfac : (H.map (prod.fst : W ⨯ U ⟶ W)).left =
      ((prodComparison H W U).left ≫
        (Over.prodLeftIsoPullback (H.obj W) (H.obj U)).hom) ≫
          pullback.fst (H.obj W).hom (H.obj U).hom := by
    rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst, ← prodComparison_fst H W U]
    rfl
  have h1 : IsFinite (H.obj U).hom := hU
  have h2 : Etale (H.obj U).hom := U.property
  have hfin : IsFinite (pullback.fst (H.obj W).hom (H.obj U).hom) := inferInstance
  have het : Etale (pullback.fst (H.obj W).hom (H.obj U).hom) := inferInstance
  have hcl : IsIso (prodComparison H W U).left :=
    inferInstanceAs (IsIso ((Over.forget X.1).map (prodComparison H W U)))
  have hisoc : IsIso ((prodComparison H W U).left ≫
      (Over.prodLeftIsoPullback (H.obj W) (H.obj U)).hom) := inferInstance
  show IsFinite (H.map (prod.fst : W ⨯ U ⟶ W)).left ∧
    Etale (H.map (prod.fst : W ⨯ U ⟶ W)).left
  rw [hfac]
  exact ⟨inferInstance, inferInstance⟩

/-- **The local representatives of a finite locally constant sheaf, in the slices.** A finite
locally constant sheaf of sets on the small étale site of `X` has a covering `{V i ⟶ X}` on each
member of which its restriction to the localized site is represented by an object of the slice
`Over (V i)` whose underlying morphism of schemes is finite étale.

On a member of a trivializing covering the sheaf is constant with finite value `E`; the constant
sheaf on `E` is represented over `X` by a disjoint union of `E` copies of `X`
(`Stacks.EtaleCohomology.exists_finiteEtaleRepresentable_constantSheaf`), and the restriction of
a representable sheaf to a slice is represented by the product with the slicing object. -/
public theorem exists_sliceRepresentatives_of_isFiniteLocallyConstant
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)))
    (hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) F) :
    ∃ (I : Type (u + 1)) (V : I → SmallEtale B X.1 X.2)
      (f : ∀ i, V i ⟶ SmallEtale.final B X.1 X.2),
      Sieve.ofArrows V f ∈
          SmallEtale.topology B X.1 X.2 (SmallEtale.final B X.1 X.2) ∧
        ∀ i, ∃ A : Over (V i),
          IsFinite ((smallEtaleToOver B X).map A.hom).left ∧
            Etale ((smallEtaleToOver B X).map A.hom).left ∧
            Nonempty (F.over (V i) ≅
              ((SmallEtale.topology B X.1 X.2).over (V i)).uliftYoneda.{u + 1}.obj A) := by
  set J := SmallEtale.topology B X.1 X.2 with hJ
  obtain ⟨I, V, f, hf, hlocal⟩ := hF.exists_finite_cover (SmallEtale.final B X.1 X.2)
  refine ⟨I, V, f, hf, fun i ↦ ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := hlocal i
  have : Finite E := hE
  obtain ⟨U, hU, ⟨eU⟩⟩ := exists_finiteEtaleRepresentable_constantSheaf B X.2 E
  obtain ⟨hfin, het⟩ := isFinite_etale_left_map_prodFst B X (V i) U hU
  exact ⟨Over.mk (prod.fst : V i ⨯ U ⟶ V i), hfin, het,
    ⟨e.symm ≪≫
      ((Stacks.ConstantSheaf.overPullbackConstantSheafIsoType.{u + 1} J
        (SmallEtale.finalIsTerminal B X.1 X.2) (V i)).app E).symm ≪≫
      (J.overPullback (Type (u + 1)) (V i)).mapIso
        (eU ≪≫ sheafifiedYonedaIsoUliftYoneda J U) ≪≫
      overUliftYonedaIso J (V i) U⟩⟩

/-! ### The descent datum attached to a family of local representatives -/

/-- A family whose sieve covers the final object of the small étale site covers the topos. -/
private theorem coversTop_of_ofArrows_mem_final
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    {I : Type (u + 1)} (V : I → SmallEtale B X.1 X.2)
    (f : ∀ i, V i ⟶ SmallEtale.final B X.1 X.2)
    (hf : Sieve.ofArrows V f ∈
      SmallEtale.topology B X.1 X.2 (SmallEtale.final B X.1 X.2)) :
    (SmallEtale.topology B X.1 X.2).CoversTop V := by
  refine ((SmallEtale.topology B X.1 X.2).coversTop_iff_of_isTerminal _
    (SmallEtale.finalIsTerminal B X.1 X.2) V).mpr ?_
  refine (SmallEtale.topology B X.1 X.2).superset_covering ?_ hf
  intro Z g hg
  obtain ⟨i, k, _⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  exact ⟨i, ⟨k⟩⟩

/-- **A covering of the final object of the small étale site is an fpqc covering of `X`.** It is
an étale covering of schemes, étale coverings are fppf coverings and fppf coverings are fpqc
coverings. -/
public theorem smallEtale_cover_isFpqc
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    {I : Type (u + 1)} (V : I → SmallEtale B X.1 X.2)
    (f : ∀ i, V i ⟶ SmallEtale.final B X.1 X.2)
    (hf : Sieve.ofArrows V f ∈
      SmallEtale.topology B X.1 X.2 (SmallEtale.final B X.1 X.2)) :
    Presieve.ofArrows (fun i ↦ (SmallEtale.toScheme B X.1 X.2).obj (V i))
      (fun i ↦ B.inclusion.map (V i).obj.hom) ∈ Scheme.fpqcPrecoverage X.1 := by
  exact SmallEtale.presieve₀_mem_fpqcPrecoverage_coveringHypercover B X.1 X.2 V
    (coversTop_of_ofArrows_mem_final B X V f hf)

/-- **The descent datum of a family of local representatives.** The transitions of
`Stacks.EtaleCohomology.localTransitionIso`, carried into schemes over `X` by the
product-preserving embedding of the small étale site, are the gluing isomorphisms of a descent
datum relative to the covering family. -/
public noncomputable def localRepresentativesDescentData
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)))
    {I : Type (u + 1)} (V : I → SmallEtale B X.1 X.2)
    (A : ∀ i, Over (V i))
    (e : ∀ i, F.over (V i) ≅
      ((SmallEtale.topology B X.1 X.2).over (V i)).uliftYoneda.{u + 1}.obj (A i)) :
    DescentData (fun i ↦ B.inclusion.map (V i).obj.hom) := by
  have hH := smallEtaleToOver_preservesBinaryProducts B X
  let H := smallEtaleToOver B X
  refine descentDataOfTransitions (fun i ↦ (H.obj (V i)).left)
    (fun i ↦ (H.obj (V i)).hom)
    (fun i ↦ H.obj (A i).left) (fun i ↦ H.map (A i).hom)
    (fun i j ↦ mapProductIso H (localTransitionIso (e i) (e j))) ?_ ?_
  · intro i j
    change (mapProductIso H (localTransitionIso (e i) (e j))).hom ≫
      prod.map (𝟙 (H.obj (V i))) (H.map (A j).hom) =
        prod.map (H.map (A i).hom) (𝟙 (H.obj (V j)))
    apply (cancel_epi (prodComparison H (A i).left (V j))).mp
    rw [← Category.assoc, prodComparison_mapProductIso,
      Category.assoc, ← H.map_id (V i), ← prodComparison_natural,
      ← Category.assoc, ← H.map_comp]
    have hh : (localTransitionIso (e i) (e j)).hom ≫
        prod.map (𝟙 _) (A j).hom = prod.map (A i).hom (𝟙 _) := by
      apply prod.hom_ext <;> simp [localTransitionIso,
        localTransition_fst, localTransition_base]
    rw [hh, prodComparison_natural, H.map_id]
  · exact mapProductIso_cocycle H V (fun i ↦ (A i).left)
      (fun i j ↦ localTransitionIso (e i) (e j))
      (fun i j k ↦ localTransition_cocycle (e i) (e j) (e k))

/-! ### The projections supplied by a chart -/

section Chart

variable {S : Scheme.{u}} {I : Type v} {V : I → Scheme.{u}} {f : ∀ i, V i ⟶ S}
  {D : DescentData f}

/-- The projection of a component of a descent datum onto the base of a chart, read as a
morphism of schemes over `S`. -/
public noncomputable def chartProj (C : D.Chart) (i : I) :
    (Over.map (f i)).obj (D.obj i) ⟶ C.base :=
  Over.homMk (C.proj i) (C.isPullback i).w

/-- The underlying morphism of schemes of `Stacks.EtaleCohomology.chartProj`. -/
@[simp]
public lemma chartProj_left (C : D.Chart) (i : I) : (chartProj C i).left = C.proj i := rfl

/-- **The projections of a chart are compatible with the gluing isomorphisms of the datum**,
expressed with the binary products of `Over S` rather than with fibre products of schemes. -/
public lemma chartProj_gluing (C : D.Chart) (i j : I) :
    (D.gluing i j).hom.left ≫ prod.snd ≫ chartProj C j = prod.fst ≫ chartProj C i := by
  apply Over.OverMorphism.ext
  have e₂ : (Over.prodLeftIsoPullback (Over.mk (f i))
        ((Over.map (f j)).obj (D.obj j))).hom ≫
        pullback.snd (f i) ((D.obj j).hom ≫ f j) =
      (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_snd _ _
  have e₁ : (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i))
        (Over.mk (f j))).hom ≫
        pullback.fst ((D.obj i).hom ≫ f i) (f j) =
      (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _).left :=
    Over.prodLeftIsoPullback_hom_fst _ _
  have h : (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i))
        (Over.mk (f j))).inv ≫ (D.gluing i j).hom.left.left ≫
        (Over.prodLeftIsoPullback (Over.mk (f i))
          ((Over.map (f j)).obj (D.obj j))).hom ≫
        pullback.snd (f i) ((D.obj j).hom ≫ f j) ≫ C.proj j =
      pullback.fst ((D.obj i).hom ≫ f i) (f j) ≫ C.proj i := by
    simpa only [DescentData.gluingPullbackIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Over.forget_map, Category.assoc] using C.compat i j
  have h2 := congrArg (fun k ↦ (Over.prodLeftIsoPullback
    ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).hom ≫ k) h
  simp only [Iso.hom_inv_id_assoc] at h2
  show (D.gluing i j).hom.left.left ≫
    (prod.snd : Over.mk (f i) ⨯ (Over.map (f j)).obj (D.obj j) ⟶ _).left ≫ C.proj j =
      (prod.fst : (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j) ⟶ _).left ≫ C.proj i
  rw [← e₂, ← e₁]
  simpa only [Category.assoc] using h2

attribute [local implicit_reducible] descentDataOfTransitions in
/-- The projections of a chart of a descent datum built from transitions are compatible with
those transitions. -/
public lemma chartProj_transitions
    (Y : I → Over S) (p : ∀ i, Y i ⟶ Over.mk (f i))
    (t : ∀ i j, Y i ⨯ Over.mk (f j) ≅ Over.mk (f i) ⨯ Y j)
    (hp : ∀ i j, (t i j).hom ≫ prod.map (𝟙 _) (p j) = prod.map (p i) (𝟙 _))
    (ht : ∀ i j k, prod.map (t i j).hom (𝟙 (Over.mk (f k))) ≫
      prodMapLastTwo (t j k).hom = prodMapFirstThird (t i k).hom)
    (C : (descentDataOfTransitions V f Y p t hp ht).Chart) (i j : I) :
    (t i j).hom ≫ prod.snd ≫ (componentTotalIso (p j)).inv ≫ chartProj C j =
      prod.fst ≫ (componentTotalIso (p i)).inv ≫ chartProj C i := by
  have h : (prod.map (componentTotalIso (p i)).hom (𝟙 (Over.mk (f j))) ≫
        (t i j).hom ≫ prod.map (𝟙 (Over.mk (f i))) (componentTotalIso (p j)).inv) ≫
      prod.snd ≫ chartProj C j = prod.fst ≫ chartProj C i := chartProj_gluing C i j
  have hm : IsIso (prod.map (componentTotalIso (p i)).hom (𝟙 (Over.mk (f j)))) :=
    ⟨prod.map (componentTotalIso (p i)).inv (𝟙 (Over.mk (f j))), by simp, by simp⟩
  have hL : prod.map (componentTotalIso (p i)).hom (𝟙 (Over.mk (f j))) ≫
        (t i j).hom ≫ prod.snd ≫ (componentTotalIso (p j)).inv ≫ chartProj C j =
      (prod.map (componentTotalIso (p i)).hom (𝟙 (Over.mk (f j))) ≫
          (t i j).hom ≫ prod.map (𝟙 (Over.mk (f i))) (componentTotalIso (p j)).inv) ≫
        prod.snd ≫ chartProj C j := by
    simp only [Category.assoc, prod.map_snd_assoc]
  have hR : prod.map (componentTotalIso (p i)).hom (𝟙 (Over.mk (f j))) ≫
        prod.fst ≫ (componentTotalIso (p i)).inv ≫ chartProj C i =
      prod.fst ≫ chartProj C i := by
    rw [prod.map_fst_assoc, Iso.hom_inv_id_assoc]
    rfl
  exact (cancel_epi (prod.map (componentTotalIso (p i)).hom (𝟙 (Over.mk (f j))))).mp
    (hL.trans (h.trans hR.symm))

end Chart

/-! ### The projection of a local representative -/

attribute [local implicit_reducible] descentDataOfTransitions localRepresentativesDescentData

section LocalProjection

variable (B : BigEtaleSite.{u}) (X : B.Scheme)
  (F : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)))
  {I : Type (u + 1)} (V : I → SmallEtale B X.1 X.2) (A : ∀ i, Over (V i))
  (e : ∀ i, F.over (V i) ≅
    ((SmallEtale.topology B X.1 X.2).over (V i)).uliftYoneda.{u + 1}.obj (A i))

/-- The projection of a local representative onto the descended object, read in schemes over
`X`. -/
public noncomputable def localRepresentativeProjection
    (C : (localRepresentativesDescentData B X F V A e).Chart) (i : I) :
    (smallEtaleToOver B X).obj (A i).left ⟶ C.base :=
  (componentTotalIso ((smallEtaleToOver B X).map (A i).hom)).inv ≫ chartProj C i

/-- **The projections of the local representatives are compatible with the transitions.** -/
public lemma localRepresentativeProjection_transition
    (C : (localRepresentativesDescentData B X F V A e).Chart) (i j : I) :
    (smallEtaleToOver B X).map (localTransition (e i) (e j)) ≫
        (smallEtaleToOver B X).map prod.snd ≫
          localRepresentativeProjection B X F V A e C j =
      (smallEtaleToOver B X).map prod.fst ≫
        localRepresentativeProjection B X F V A e C i := by
  have hH := smallEtaleToOver_preservesBinaryProducts B X
  set H := smallEtaleToOver B X with hHdef
  have hp : ∀ i j, (mapProductIso H (localTransitionIso (e i) (e j))).hom ≫
      prod.map (𝟙 (H.obj (V i))) (H.map (A j).hom) =
        prod.map (H.map (A i).hom) (𝟙 (H.obj (V j))) := by
    intro i j
    apply (cancel_epi (prodComparison H (A i).left (V j))).mp
    rw [← Category.assoc, prodComparison_mapProductIso,
      Category.assoc, ← H.map_id (V i), ← prodComparison_natural,
      ← Category.assoc, ← H.map_comp]
    have hh : (localTransitionIso (e i) (e j)).hom ≫
        prod.map (𝟙 _) (A j).hom = prod.map (A i).hom (𝟙 _) := by
      apply prod.hom_ext <;> simp [localTransitionIso,
        localTransition_fst, localTransition_base]
    rw [hh, prodComparison_natural, H.map_id]
  have ht := mapProductIso_cocycle H V (fun i ↦ (A i).left)
    (fun i j ↦ localTransitionIso (e i) (e j))
    (fun i j k ↦ localTransition_cocycle (e i) (e j) (e k))
  have h := chartProj_transitions (fun i ↦ H.obj (A i).left) (fun i ↦ H.map (A i).hom)
    (fun i j ↦ mapProductIso H (localTransitionIso (e i) (e j))) hp ht C i j
  have hcmp : prodComparison H (A i).left (V j) ≫
      (mapProductIso H (localTransitionIso (e i) (e j))).hom =
        H.map (localTransition (e i) (e j)) ≫ prodComparison H (V i) (A j).left :=
    prodComparison_mapProductIso H (localTransitionIso (e i) (e j))
  have hs : prodComparison H (V i) (A j).left ≫
      (prod.snd : H.obj (V i) ⨯ H.obj (A j).left ⟶ _) = H.map prod.snd :=
    prodComparison_snd H (V i) (A j).left
  have hf : prodComparison H (A i).left (V j) ≫
      (prod.fst : H.obj (A i).left ⨯ H.obj (V j) ⟶ _) = H.map prod.fst :=
    prodComparison_fst H (A i).left (V j)
  show H.map (localTransition (e i) (e j)) ≫ H.map prod.snd ≫
      (componentTotalIso (H.map (A j).hom)).inv ≫ chartProj C j =
    H.map prod.fst ≫ (componentTotalIso (H.map (A i).hom)).inv ≫ chartProj C i
  calc H.map (localTransition (e i) (e j)) ≫ H.map prod.snd ≫
        (componentTotalIso (H.map (A j).hom)).inv ≫ chartProj C j
      = H.map (localTransition (e i) (e j)) ≫
          (prodComparison H (V i) (A j).left ≫ prod.snd) ≫
            (componentTotalIso (H.map (A j).hom)).inv ≫ chartProj C j := by rw [hs]
    _ = (H.map (localTransition (e i) (e j)) ≫ prodComparison H (V i) (A j).left) ≫
          prod.snd ≫ (componentTotalIso (H.map (A j).hom)).inv ≫ chartProj C j := by
          simp only [Category.assoc]
    _ = (prodComparison H (A i).left (V j) ≫
          (mapProductIso H (localTransitionIso (e i) (e j))).hom) ≫
          prod.snd ≫ (componentTotalIso (H.map (A j).hom)).inv ≫ chartProj C j := by
          rw [hcmp]
    _ = prodComparison H (A i).left (V j) ≫
          ((mapProductIso H (localTransitionIso (e i) (e j))).hom ≫
            prod.snd ≫ (componentTotalIso (H.map (A j).hom)).inv ≫ chartProj C j) := by
          simp only [Category.assoc]
    _ = prodComparison H (A i).left (V j) ≫
          (prod.fst ≫ (componentTotalIso (H.map (A i).hom)).inv ≫ chartProj C i) :=
          congrArg (fun k ↦ prodComparison H (A i).left (V j) ≫ k) h
    _ = (prodComparison H (A i).left (V j) ≫ prod.fst) ≫
          (componentTotalIso (H.map (A i).hom)).inv ≫ chartProj C i := by
          simp only [Category.assoc]
    _ = H.map prod.fst ≫ (componentTotalIso (H.map (A i).hom)).inv ≫ chartProj C i := by
          rw [hf]

/-- **The sections determine the projection.** If two local representatives receive the same
section of `F` from the same object of the site, the two morphisms they give to the descended
object agree. -/
public lemma localRepresentativeProjection_lift
    (C : (localRepresentativesDescentData B X F V A e).Chart)
    {Z : SmallEtale B X.1 X.2} (i j : I)
    (g₁ : Z ⟶ V i) (g₂ : Z ⟶ V j) (s : F.obj.obj (Opposite.op Z)) :
    (smallEtaleToOver B X).map (localLift (e i) g₁ s) ≫
        localRepresentativeProjection B X F V A e C i =
      (smallEtaleToOver B X).map (localLift (e j) g₂ s) ≫
        localRepresentativeProjection B X F V A e C j := by
  set H := smallEtaleToOver B X with hHdef
  have h : H.map (prod.lift (localLift (e i) g₁ s) g₂) ≫
        H.map (localTransition (e i) (e j)) ≫ H.map prod.snd ≫
          localRepresentativeProjection B X F V A e C j =
      H.map (prod.lift (localLift (e i) g₁ s) g₂) ≫
        H.map prod.fst ≫ localRepresentativeProjection B X F V A e C i := by
    rw [localRepresentativeProjection_transition]
  have ht : prod.lift (localLift (e i) g₁ s) g₂ ≫ localTransition (e i) (e j) ≫
      prod.snd = localLift (e j) g₂ s := by
    apply localSection_hom_ext (e j)
    · simp only [Category.assoc, localTransition_base, prod.lift_snd, localLift_hom]
    · rw [localTransition_section_precomp]
      simp [localSection_localLift]
  rw [← H.map_comp_assoc, ← H.map_comp_assoc, Category.assoc, ht,
    ← H.map_comp_assoc, prod.lift_fst] at h
  exact h.symm

end LocalProjection

/-! ### The representing object and the isomorphism of sheaves -/

/-- The embedding of the small étale site into schemes over `X` is fully faithful. -/
public noncomputable def smallEtaleToOverFullyFaithful (B : BigEtaleSite.{u}) (X : B.Scheme) :
    (smallEtaleToOver B X).FullyFaithful :=
  ((BigEtaleOver.IsEtaleOver B X.1 X.2).fullyFaithfulι).comp
    (Functor.FullyFaithful.over (B.obj X.1 X.2) B.inclusion
      (schemeSizeBelow B.cutoff).fullyFaithfulι)

section FinalIso

variable (B : BigEtaleSite.{u}) (X : B.Scheme)
  (F : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)))
  {I : Type (u + 1)} (V : I → SmallEtale B X.1 X.2) (A : ∀ i, Over (V i))
  (e : ∀ i, F.over (V i) ≅
    ((SmallEtale.topology B X.1 X.2).over (V i)).uliftYoneda.{u + 1}.obj (A i))
  (C : (localRepresentativesDescentData B X F V A e).Chart)
  (W : SmallEtale B X.1 X.2) (w : (smallEtaleToOver B X).obj W ≅ C.base)

/-- The morphism of the small étale site from a local representative to the representing
object: the projection onto the base of the chart, read through the full embedding into schemes
over `X`. -/
public noncomputable def representingHomOfChart (i : I) : (A i).left ⟶ W :=
  (smallEtaleToOverFullyFaithful B X).preimage
    (localRepresentativeProjection B X F V A e C i ≫ w.inv)

/-- `Stacks.EtaleCohomology.representingHomOfChart` is the projection onto the representing
object. -/
public lemma map_representingHomOfChart (i : I) :
    (smallEtaleToOver B X).map (representingHomOfChart B X F V A e C W w i) =
      localRepresentativeProjection B X F V A e C i ≫ w.inv :=
  (smallEtaleToOverFullyFaithful B X).map_preimage _

/-- **Each local representative is the product of its base with the representing object.** -/
public theorem isIso_lift_representingHomOfChart (i : I) :
    IsIso (prod.lift (A i).hom (representingHomOfChart B X F V A e C W w i)) := by
  have hH := smallEtaleToOver_preservesBinaryProducts B X
  have hpb : IsPullback (((smallEtaleToOver B X).map (A i).hom).left)
      (C.proj i ≫ w.inv.left) (((smallEtaleToOver B X).obj (V i)).hom)
      (((smallEtaleToOver B X).obj W).hom) :=
    (C.isPullback i).flip.of_iso (Iso.refl _) (Iso.refl _)
      (((Over.forget X.1).mapIso w).symm) (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.id_comp]; rfl)
      (by simp only [Iso.refl_hom, Category.id_comp]; rfl)
      (by simp only [Iso.refl_hom, Category.comp_id]; rfl)
      (by simp; exact (Over.w w.inv).symm)
  have hcmp : IsIso (prodComparison (smallEtaleToOver B X) (V i) W) := inferInstance
  have hfst : (prod.lift ((smallEtaleToOver B X).map (A i).hom)
        ((smallEtaleToOver B X).map (representingHomOfChart B X F V A e C W w i))).left ≫
      ((Over.prodLeftIsoPullback ((smallEtaleToOver B X).obj (V i))
          ((smallEtaleToOver B X).obj W)).hom ≫
        pullback.fst ((smallEtaleToOver B X).obj (V i)).hom
          ((smallEtaleToOver B X).obj W).hom) =
      ((smallEtaleToOver B X).map (A i).hom).left := by
    rw [Over.prodLeftIsoPullback_hom_fst, ← Over.comp_left, prod.lift_fst]
  have hsnd : (prod.lift ((smallEtaleToOver B X).map (A i).hom)
        ((smallEtaleToOver B X).map (representingHomOfChart B X F V A e C W w i))).left ≫
      ((Over.prodLeftIsoPullback ((smallEtaleToOver B X).obj (V i))
          ((smallEtaleToOver B X).obj W)).hom ≫
        pullback.snd ((smallEtaleToOver B X).obj (V i)).hom
          ((smallEtaleToOver B X).obj W).hom) =
      C.proj i ≫ w.inv.left := by
    rw [Over.prodLeftIsoPullback_hom_snd, ← Over.comp_left, prod.lift_snd,
      map_representingHomOfChart]
    simp [localRepresentativeProjection, componentTotalIso, chartProj]
  have hn : (prod.lift ((smallEtaleToOver B X).map (A i).hom)
        ((smallEtaleToOver B X).map (representingHomOfChart B X F V A e C W w i))).left ≫
      (Over.prodLeftIsoPullback ((smallEtaleToOver B X).obj (V i))
        ((smallEtaleToOver B X).obj W)).hom = hpb.isoPullback.hom := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, hpb.isoPullback_hom_fst]
    · rw [Category.assoc, hsnd, hpb.isoPullback_hom_snd]
  have h1 : IsIso ((prod.lift ((smallEtaleToOver B X).map (A i).hom)
        ((smallEtaleToOver B X).map (representingHomOfChart B X F V A e C W w i))).left ≫
      (Over.prodLeftIsoPullback ((smallEtaleToOver B X).obj (V i))
        ((smallEtaleToOver B X).obj W)).hom) := by
    rw [hn]; infer_instance
  have h2 : IsIso (prod.lift ((smallEtaleToOver B X).map (A i).hom)
      ((smallEtaleToOver B X).map (representingHomOfChart B X F V A e C W w i))).left :=
    IsIso.of_isIso_comp_right _ (Over.prodLeftIsoPullback ((smallEtaleToOver B X).obj (V i))
      ((smallEtaleToOver B X).obj W)).hom
  have h3 : IsIso (prod.lift ((smallEtaleToOver B X).map (A i).hom)
      ((smallEtaleToOver B X).map (representingHomOfChart B X F V A e C W w i))) :=
    have h2' : IsIso ((Over.forget X.1).map (prod.lift ((smallEtaleToOver B X).map (A i).hom)
        ((smallEtaleToOver B X).map (representingHomOfChart B X F V A e C W w i)))) := h2
    isIso_of_reflects_iso _ (Over.forget X.1)
  have h4 : (smallEtaleToOver B X).map
        (prod.lift (A i).hom (representingHomOfChart B X F V A e C W w i)) ≫
      prodComparison (smallEtaleToOver B X) (V i) W =
    prod.lift ((smallEtaleToOver B X).map (A i).hom)
      ((smallEtaleToOver B X).map (representingHomOfChart B X F V A e C W w i)) :=
    prodComparison_lift (smallEtaleToOver B X) (A i).hom
      (representingHomOfChart B X F V A e C W w i)
  have h5 : IsIso ((smallEtaleToOver B X).map
      (prod.lift (A i).hom (representingHomOfChart B X F V A e C W w i))) := by
    have h6 : IsIso ((smallEtaleToOver B X).map
        (prod.lift (A i).hom (representingHomOfChart B X F V A e C W w i)) ≫
          prodComparison (smallEtaleToOver B X) (V i) W) := by
      rw [h4]; exact h3
    exact IsIso.of_isIso_comp_right _ (prodComparison (smallEtaleToOver B X) (V i) W)
  have := h5
  exact (smallEtaleToOverFullyFaithful B X).isIso_of_isIso_map _

/-- **Each local representative, as an object over its base, is the product with the
representing object.** -/
public noncomputable def representingProdIso (i : I) :
    A i ≅ Over.mk (prod.fst : V i ⨯ W ⟶ V i) :=
  have := isIso_lift_representingHomOfChart B X F V A e C W w i
  Over.isoMk (asIso (prod.lift (A i).hom (representingHomOfChart B X F V A e C W w i)))
    (by simp)

/-- The underlying morphism of `Stacks.EtaleCohomology.representingProdIso`. -/
public lemma representingProdIso_hom_left (i : I) :
    (representingProdIso B X F V A e C W w i).hom.left =
      prod.lift (A i).hom (representingHomOfChart B X F V A e C W w i) := rfl

/-- **The local isomorphism of sheaves.** On each member of the covering the sheaf `F` is the
sheaf represented by the representing object. -/
public noncomputable def localSheafIso (i : I) :
    F.over (V i) ≅
      ((SmallEtale.topology B X.1 X.2).uliftYoneda.{u + 1}.obj W).over (V i) :=
  e i ≪≫ ((SmallEtale.topology B X.1 X.2).over (V i)).uliftYoneda.{u + 1}.mapIso
      (representingProdIso B X F V A e C W w i) ≪≫
    (overUliftYonedaIso (SmallEtale.topology B X.1 X.2) (V i) W).symm

/-- **The local isomorphism on sections.** It sends a section to the morphism it determines into
the local representative, followed by the projection onto the representing object. -/
public lemma localSheafIso_apply (i : I) (Z : Over (V i))
    (s : F.obj.obj (Opposite.op Z.left)) :
    ((localSheafIso B X F V A e C W w i).hom.hom.app (Opposite.op Z) s).down =
      localLift (e i) Z.hom s ≫ representingHomOfChart B X F V A e C W w i := by
  show (localLift (e i) Z.hom s ≫
      (representingProdIso B X F V A e C W w i).hom.left) ≫ prod.snd = _
  rw [representingProdIso_hom_left, Category.assoc, prod.lift_snd]

/-- **The local isomorphisms agree on overlaps.** Both are determined by the section, and a
morphism to the representing object is determined by the section it pulls back, which is
`Stacks.EtaleCohomology.localRepresentativeProjection_lift`. -/
public lemma localSheafIso_compat (Z : SmallEtale B X.1 X.2) (i j : I)
    (a : Z ⟶ V i) (b : Z ⟶ V j) :
    Functor.isoWhiskerLeft (Over.map a).op
        ((sheafToPresheaf ((SmallEtale.topology B X.1 X.2).over (V i)) (Type (u + 1))).mapIso
          (localSheafIso B X F V A e C W w i)) =
      Functor.isoWhiskerLeft (Over.map b).op
        ((sheafToPresheaf ((SmallEtale.topology B X.1 X.2).over (V j)) (Type (u + 1))).mapIso
          (localSheafIso B X F V A e C W w j)) := by
  have hFF := smallEtaleToOverFullyFaithful B X
  refine Iso.ext ?_
  ext T s
  refine ULift.ext ?_
  show ((localSheafIso B X F V A e C W w i).hom.hom.app
      (Opposite.op ((Over.map a).obj T.unop)) s).down =
    ((localSheafIso B X F V A e C W w j).hom.hom.app
      (Opposite.op ((Over.map b).obj T.unop)) s).down
  refine (localSheafIso_apply B X F V A e C W w i ((Over.map a).obj T.unop) s).trans
    (Eq.trans ?_
      (localSheafIso_apply B X F V A e C W w j ((Over.map b).obj T.unop) s).symm)
  refine hFF.map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, map_representingHomOfChart,
    map_representingHomOfChart, ← Category.assoc, ← Category.assoc]
  exact congrArg (fun k ↦ k ≫ w.inv)
    (localRepresentativeProjection_lift B X F V A e C i j
      ((Over.map a).obj T.unop).hom ((Over.map b).obj T.unop).hom s)

/-- **The sheaf is represented by the descended object.** -/
public noncomputable def sheafIsoUliftYonedaOfChart
    (hV : (SmallEtale.topology B X.1 X.2).CoversTop V) :
    F ≅ (SmallEtale.topology B X.1 X.2).uliftYoneda.{u + 1}.obj W :=
  sheafIsoOfCompatibleLocalIsos (SmallEtale.topology B X.1 X.2) F _ V hV
    (fun i ↦ (sheafToPresheaf ((SmallEtale.topology B X.1 X.2).over (V i))
      (Type (u + 1))).mapIso (localSheafIso B X F V A e C W w i))
    (fun Z i j a b ↦ localSheafIso_compat B X F V A e C W w Z i j a b)

end FinalIso

/-! ### Tag 03RV -/

/-- A covering family of the final object of the small étale site covers the topos. -/
public theorem coversTop_of_cover_final
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    {I : Type (u + 1)} (V : I → SmallEtale B X.1 X.2)
    (f : ∀ i, V i ⟶ SmallEtale.final B X.1 X.2)
    (hf : Sieve.ofArrows V f ∈
      SmallEtale.topology B X.1 X.2 (SmallEtale.final B X.1 X.2)) :
    (SmallEtale.topology B X.1 X.2).CoversTop V :=
  coversTop_of_ofArrows_mem_final B X V f hf

/-- **Local representatives in the slices descend.** A sheaf of sets on the small étale site of
`X` which, over each member `V i` of a covering of the final object, is represented in the
localized site by an object of the slice `Over (V i)` with finite étale structure morphism, is
represented by an object of the site with finite structure morphism.

The local representatives form a descent datum relative to the covering
(`Stacks.EtaleCohomology.localRepresentativesDescentData`), which is effective by Stacks 0245;
the descended scheme is finite étale over `X`, and the local isomorphisms glue. -/
public theorem exists_finiteEtaleRepresentable_of_sliceRepresentatives
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1)))
    {I : Type (u + 1)} (V : I → SmallEtale B X.1 X.2)
    (f : ∀ i, V i ⟶ SmallEtale.final B X.1 X.2)
    (hcov : Sieve.ofArrows V f ∈
      SmallEtale.topology B X.1 X.2 (SmallEtale.final B X.1 X.2))
    (A : ∀ i, Over (V i))
    (hAfin : ∀ i, IsFinite ((smallEtaleToOver B X).map (A i).hom).left)
    (hAet : ∀ i, Etale ((smallEtaleToOver B X).map (A i).hom).left)
    (e : ∀ i, F.over (V i) ≅
      ((SmallEtale.topology B X.1 X.2).over (V i)).uliftYoneda.{u + 1}.obj (A i)) :
    ∃ U : SmallEtale B X.1 X.2,
      IsFinite (B.inclusion.map U.obj.hom) ∧
        Nonempty (F ≅
          (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.2)).obj U) := by
  classical
  have hfpqc := smallEtale_cover_isFpqc B X V f hcov
  obtain ⟨U, hd, hUfin, hUet⟩ := exists_finiteEtale_of_descentData
    (fun i ↦ B.inclusion.map (V i).obj.hom) hfpqc
    (localRepresentativesDescentData B X F V A e)
    (fun i ↦ hAfin i) (fun i ↦ hAet i)
  obtain ⟨d⟩ := hd
  obtain ⟨W, hWfin, hw⟩ := exists_smallSiteObject_of_finiteEtale B X U hUfin hUet
  obtain ⟨w₀⟩ := hw
  refine ⟨W, hWfin, ⟨?_⟩⟩
  exact sheafIsoUliftYonedaOfChart B X F V A e
      (DescentData.Chart.ofIsoCanonicalDatum U d.symm) W w₀
      (coversTop_of_cover_final B X V f hcov) ≪≫
    (sheafifiedYonedaIsoUliftYoneda (SmallEtale.topology B X.1 X.2) W).symm

/-- **Stacks Project, Tag 03RV.** A sheaf of sets on the small étale site of `X` is finite
locally constant if and only if it is represented by an object of the site whose structure
morphism is finite — that is, by a scheme finite étale over `X`.

The reverse implication is
`Stacks.EtaleCohomology.isFiniteLocallyConstant_of_finiteEtaleRepresentable`. The forward one is
the étale-local representability of
`Stacks.EtaleCohomology.exists_sliceRepresentatives_of_isFiniteLocallyConstant` followed by
effective descent for schemes affine over the base along an fpqc covering, Stacks 0245, in the
form `AlgebraicGeometry.DescentData.isFamilyEffective_of_isAffineHom_of_anyIndex`. -/
@[stacks 03RV, sga "4 IX 2.2"]
public theorem isFiniteLocallyConstant_iff_finiteEtaleRepresentable
    (B : BigEtaleSite.{u}) (X : B.Scheme)
    (F : Sheaf (SmallEtale.topology B X.1 X.2) (Type (u + 1))) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B X.1 X.2) F ↔
      ∃ U : SmallEtale B X.1 X.2,
        IsFinite (B.inclusion.map U.obj.hom) ∧
          Nonempty (F ≅
            (Sheaf.sheafifiedYoneda (SmallEtale.topology B X.1 X.2)).obj U) := by
  refine ⟨fun hF ↦ ?_, isFiniteLocallyConstant_of_finiteEtaleRepresentable B X F⟩
  obtain ⟨I, V, f, hcov, hlocal⟩ :=
    exists_sliceRepresentatives_of_isFiniteLocallyConstant B X F hF
  choose A hAfin hAet he using hlocal
  exact exists_finiteEtaleRepresentable_of_sliceRepresentatives B X F V f hcov A hAfin hAet
    (fun i ↦ (he i).some)

end Stacks.EtaleCohomology

end
