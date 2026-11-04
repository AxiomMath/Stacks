module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ShriekTrianglesData
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroOpenCovariance

/-!
# The map from compactly supported cohomology of an open to the cohomology of a proper scheme

Let `p : X ⟶ Y` be a proper morphism to a Noetherian scheme, `U ⊆ X` an open subscheme with
inclusion `j : U ⟶ X`, and `g = p ∘ j : U ⟶ Y`. Then `X` is a compactification of `U` over `Y`, so
`Rg_! = Rp_* ∘ Rj_!` ([Stacks, Section 0G4Z]), and [Stacks, Tag 0G56] gives a canonical map

`Rg_!(K|_U) ⟶ Rp_! K = Rp_* K`

functorial in `K ∈ D^b_{Coh}(𝒪_X)`. This file constructs this map in the form [Stacks, Tag 0G56]
calls the second construction, with `X` its own compactification: `Rp_*` applied to the map
`Rj_!(K|_U) ⟶ K` of [Stacks, Tag 0G4Y].

The map `Rj_!(K|_U) ⟶ K` is [Stacks, Tag 0G4Y] for the opens `U ⊆ X` of `X`
(`AlgebraicGeometry.extensionByZeroOpenCovariance` at `U ≤ ⊤`), followed by the identification of
`Rj_!` along the open `⊤ ⟶ X` with the identity: under the adjointness of [Stacks, Tag 0G4N] the
morphism `R(⊤ ⟶ X)_!(K|_⊤) ⟶ K` corresponding to the identity of `K|_⊤`.
`AlgebraicGeometry.extensionByZeroHomEquiv_extensionByZeroCounit` records that the composite
corresponds to the identity of `K|_U`, which is what pins it down.

The map of [Stacks, Tag 0G56] for an arbitrary compactification of `X` over `Y` (and the
agreement of the three constructions of the source) is not treated here; a general version
should be built on the same two ingredients, `AlgebraicGeometry.extensionByZeroOpenCovariance` and
`CategoryTheory.ProSeq.mapConst`, rather than in parallel.

## Main definitions

* `CategoryTheory.ProSeq.mapConst`: `ProSeq.map F` applied to a morphism `P ⟶ L` into a constant
  pro-object, read as a morphism into the constant pro-object at `F L`.
* `AlgebraicGeometry.extensionByZeroCounit`: the map `Rj_!(K|_U) ⟶ K` of [Stacks, Tag 0G4Y].
* `AlgebraicGeometry.lowerShriekToProperPushforward`: the map `Rg_!(K|_U) ⟶ Rp_* K` of
  [Stacks, Tag 0G56] for `X` its own compactification.

## Main results

* `CategoryTheory.ProSeq.homConstEquiv_comp`: composing with a morphism of pro-objects acts on
  morphisms into a constant pro-object through the functors of points.
* `CategoryTheory.ProSeq.constHomComponent`, `CategoryTheory.ProSeq.constHom_ext`,
  `CategoryTheory.ProSeq.constHomMk`: a morphism from a constant pro-object `L` to the pro-object
  of an inverse sequence `(N_n)` is a compatible family `L ⟶ N_n`, i.e. an element of
  `lim_n Hom(L, N_n)`.
* `CategoryTheory.ProSeq.mapOfIso_inv_app_lanUnit_app`: `ProSeq.map F` on the class of a morphism
  `M_n ⟶ L`.
* `AlgebraicGeometry.extensionByZeroHomEquiv_extensionByZeroCounit`: under
  `Hom_{Pro}(Rj_!(K|_U), K) = Hom_U(K|_U, K|_U)` the map `Rj_!(K|_U) ⟶ K` is the identity.

## References

* [Stacks Project, Tag 0G56](https://stacks.math.columbia.edu/tag/0G56)
* [Stacks Project, Tag 0G4Y](https://stacks.math.columbia.edu/tag/0G4Y)
* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u u'

namespace CategoryTheory.ProSeq

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒟' : Type u'} [Category.{v} 𝒟']

/-- Composing a morphism `g : P' ⟶ L` into a constant pro-object with a morphism `f : P ⟶ P'` of
pro-objects is, on elements of the functors of points, the action of `f` on functors of points:
the co-Yoneda lemma. -/
public lemma homConstEquiv_comp {P P' : ProSeq 𝒟} {L : 𝒟} (f : P ⟶ P')
    (g : P' ⟶ const.obj L) :
    homConstEquiv P L (f ≫ g) = f.unop.hom.app L (homConstEquiv P' L g) := by
  show coyonedaEquiv (g.unop.hom ≫ f.unop.hom) = _
  exact coyonedaEquiv_comp _ _

section Sequences

attribute [local instance] CategoryTheory.uliftCategory

/-- The lifted colimit class of `g : N_n ⟶ M` is the class `Pro.seqStage N g`. -/
public lemma seqHomColimIso_hom_app_ι (N : ℕᵒᵖ ⥤ 𝒟) (i : (ULiftHom.{v} (ULift.{v} ℕᵒᵖ))ᵒᵖ) (M : 𝒟)
    (g : (Pro.liftedInverseSequence N).obj i.unop ⟶ M) :
    (Pro.seqHomColimIso N).hom.app M
        ((colimit.ι ((Pro.liftedInverseSequence N).op ⋙ coyoneda) i).app M g) =
      Pro.seqStage N (n := (Pro.liftedIndexDown i).unop) g := by
  have h : colimit.ι ((Pro.liftedInverseSequence N).op ⋙ coyoneda) i ≫
      (Pro.seqHomColimIso N).hom =
        colimit.ι (N.op ⋙ coyoneda) (op (op (Pro.liftedIndexDown i).unop)) := by
    refine (HasColimit.ι_isoOfEquivalence_hom (F := (Pro.liftedInverseSequence N).op ⋙ coyoneda)
      (G := N.op ⋙ coyoneda) (ULiftHomULiftCategory.equiv ℕᵒᵖ).symm.op (Iso.refl _) i).trans ?_
    have hu : ((Pro.liftedInverseSequence N).op ⋙ coyoneda).map
        ((ULiftHomULiftCategory.equiv ℕᵒᵖ).symm.op.unit.app i) = 𝟙 _ :=
      Functor.map_id _ i
    refine (congrArg (· ≫ _) hu).trans ?_
    exact (Category.id_comp _).trans (Category.id_comp _)
  exact congrFun (congrArg (fun t => t.app M) h) g

variable {L : 𝒟} {N : ℕᵒᵖ ⥤ 𝒟}

/-- The `n`-th component `L ⟶ N_n` of a morphism from a constant pro-object to the pro-object of an
inverse sequence. -/
public noncomputable def constHomComponent (y : const.obj L ⟶ of N) (n : ℕ) : L ⟶ N.obj (op n) :=
  y.unop.hom.app (N.obj (op n))
    ((Pro.seqHomColimIso N).inv.app _ (Pro.seqStage N (𝟙 (N.obj (op n)))))

/-- A morphism from a constant pro-object acts on the class of `g : N_n ⟶ M` by precomposition
with its `n`-th component. -/
public lemma constHom_app_seqStage (y : const.obj L ⟶ of N) {M : 𝒟} {n : ℕ} (g : N.obj (op n) ⟶ M) :
    y.unop.hom.app M ((Pro.seqHomColimIso N).inv.app M (Pro.seqStage N g)) =
      constHomComponent y n ≫ g := by
  have h₁ : Pro.seqStage N g = (Pro.seqHomColim N).map g (Pro.seqStage N (𝟙 _)) := by
    rw [Pro.seqHomColim_map_seqStage, Category.id_comp]
  rw [h₁, NatTrans.naturality_apply]
  exact NatTrans.naturality_apply y.unop.hom g _

/-- The components of a morphism from a constant pro-object are compatible with the
transitions. -/
public lemma constHomComponent_comp_tr (y : const.obj L ⟶ of N) {n m : ℕ} (h : n ≤ m) :
    constHomComponent y m ≫ InverseSequence.tr N h = constHomComponent y n := by
  rw [← constHom_app_seqStage, Pro.seqStage_tr]
  rfl

/-- A morphism from a constant pro-object is determined by its components. -/
public lemma constHom_ext {y y' : const.obj L ⟶ of N}
    (h : ∀ n, constHomComponent y n = constHomComponent y' n) : y = y' := by
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  refine (cancel_epi (Pro.seqHomColimIso N).inv).1 ?_
  refine colimit.hom_ext fun n => ?_
  ext M g
  show y.unop.hom.app M ((Pro.seqHomColimIso N).inv.app M (Pro.seqStage N (n := n.unop.unop) g)) =
    y'.unop.hom.app M ((Pro.seqHomColimIso N).inv.app M (Pro.seqStage N (n := n.unop.unop) g))
  rw [constHom_app_seqStage, constHom_app_seqStage, h]

section Mk

variable (x : ∀ n : ℕ, L ⟶ N.obj (op n))
  (hx : ∀ n : ℕ, x (n + 1) ≫ N.map (homOfLE (Nat.le_succ n)).op = x n)

include hx in
/-- Components compatible with the successor transitions are compatible with all transitions. -/
public lemma comp_tr_of_succ {n m : ℕ} (h : n ≤ m) : x m ≫ InverseSequence.tr N h = x n := by
  induction m, h using Nat.le_induction with
  | base => simp [InverseSequence.tr]
  | succ m hnm ih =>
    have : (homOfLE (hnm.trans (Nat.le_succ m))).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
    rw [InverseSequence.tr, this, Functor.map_comp, ← Category.assoc, hx]
    exact ih

/-- The transformation `colim_n Mor(N_n, -) ⟶ Mor(L, -)` sending the class of `g : N_n ⟶ M` to
`x_n ≫ g`, for compatible `x_n : L ⟶ N_n`. -/
public noncomputable def constHomDesc (x : ∀ n : ℕ, L ⟶ N.obj (op n))
    (hx : ∀ n : ℕ, x (n + 1) ≫ N.map (homOfLE (Nat.le_succ n)).op = x n) :
    Pro.seqHomColim N ⟶ coyoneda.obj (op L) :=
  colimit.desc (N.op ⋙ coyoneda)
    { pt := coyoneda.obj (op L)
      ι :=
        { app := fun n => coyoneda.map (x n.unop.unop).op
          naturality := by
            rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ a
            have h : n ≤ m := leOfHom a.unop.unop
            obtain rfl : a = (homOfLE h).op.op := Subsingleton.elim _ _
            change coyoneda.map (InverseSequence.tr N h).op ≫ coyoneda.map (x m).op =
              coyoneda.map (x n).op ≫ 𝟙 _
            rw [Category.comp_id, ← coyoneda.map_comp, ← op_comp,
              comp_tr_of_succ x hx h] } }

/-- `CategoryTheory.ProSeq.constHomDesc x hx` sends the class of `g : N_n ⟶ M` to `x_n ≫ g`. -/
public lemma constHomDesc_app_seqStage {M : 𝒟} {n : ℕ} (g : N.obj (op n) ⟶ M) :
    (constHomDesc x hx).app M (Pro.seqStage N g) = x n ≫ g := by
  show (colimit.ι (N.op ⋙ coyoneda) (op (op n)) ≫ constHomDesc x hx).app M g = _
  rw [constHomDesc, colimit.ι_desc]
  rfl

/-- The morphism from the constant pro-object at `L` to the pro-object of `N` with given
compatible components. -/
public noncomputable def constHomMk (x : ∀ n : ℕ, L ⟶ N.obj (op n))
    (hx : ∀ n : ℕ, x (n + 1) ≫ N.map (homOfLE (Nat.le_succ n)).op = x n) :
    const.obj L ⟶ of N :=
  (ObjectProperty.homMk (X := (of N).unop) (Y := (const.obj L).unop)
    ((Pro.seqHomColimIso N).hom ≫ constHomDesc x hx)).op

/-- The components of `CategoryTheory.ProSeq.constHomMk x hx` are the `x_n`. -/
public lemma constHomComponent_constHomMk (n : ℕ) :
    constHomComponent (constHomMk x hx) n = x n := by
  show (constHomDesc x hx).app _ ((Pro.seqHomColimIso N).hom.app _
    ((Pro.seqHomColimIso N).inv.app _ (Pro.seqStage N (𝟙 (N.obj (op n)))))) = _
  rw [Iso.inv_hom_id_app_apply, constHomDesc_app_seqStage, Category.comp_id]

end Mk

/-- The lifted index of stage `n` of an inverse sequence. -/
public abbrev liftedStage (n : ℕ) : (ULiftHom.{v} (ULift.{v} ℕᵒᵖ))ᵒᵖ :=
  op ((ULift.upFunctor ⋙ ULiftHom.up).obj (op n))

/-- The class `Pro.seqStage N g` is the lifted colimit class of `g` at the lifted stage. -/
public lemma seqHomColimIso_inv_app_seqStage (N : ℕᵒᵖ ⥤ 𝒟) {M : 𝒟} {n : ℕ} (g : N.obj (op n) ⟶ M) :
    (Pro.seqHomColimIso N).inv.app M (Pro.seqStage N g) =
      (colimit.ι ((Pro.liftedInverseSequence N).op ⋙ coyoneda) (liftedStage n)).app M g :=
  (congrArg ((Pro.seqHomColimIso N).inv.app M)
    (seqHomColimIso_hom_app_ι N (liftedStage n) M g).symm).trans (Iso.hom_inv_id_app_apply _ _ _)

section Lan

variable (F : 𝒟 ⥤ 𝒟') [∀ A : 𝒟 ⥤ Type v, F.HasLeftKanExtension A]

/-- Naturality of the unit of the left Kan extension, on elements. -/
public lemma lan_map_app_lanUnit_app {A B : 𝒟 ⥤ Type v} (η : A ⟶ B) (L : 𝒟) (a : A.obj L) :
    (F.lan.map η).app (F.obj L) ((F.lanUnit.app A).app L a) =
      (F.lanUnit.app B).app L (η.app L a) :=
  (ConcreteCategory.congr_hom (congr_app (F.lanUnit.naturality η) L) a).symm

/-- Under `ProSeq.map F (of M) ≅ of (M ⋙ F)`, the image under the Kan extension unit of the class
of `g : M_n ⟶ L` is the class of `F g`. -/
public lemma mapOfIso_inv_app_lanUnit_app (M : ℕᵒᵖ ⥤ 𝒟) {L : 𝒟} {n : ℕ} (g : M.obj (op n) ⟶ L) :
    (mapOfIso F M).inv.unop.hom.app (F.obj L)
        ((F.lanUnit.app (of M).points).app L
          ((Pro.seqHomColimIso M).inv.app L (Pro.seqStage M g))) =
      (Pro.seqHomColimIso (M ⋙ F)).inv.app (F.obj L) (Pro.seqStage (M ⋙ F) (F.map g)) := by
  have h1 : (F.lan.map (Pro.seqHomColimIso M).hom).app (F.obj L)
      ((F.lanUnit.app (of M).points).app L
        ((Pro.seqHomColimIso M).inv.app L (Pro.seqStage M g))) =
        (F.lanUnit.app (Pro.seqHomColim M)).app L (Pro.seqStage M g) :=
    (lan_map_app_lanUnit_app F _ L _).trans
      (congrArg ((F.lanUnit.app (Pro.seqHomColim M)).app L) (Iso.inv_hom_id_app_apply _ _ _))
  have h2 : (Pro.lanSeqHomColimIso F M).hom.app (F.obj L)
      ((F.lanUnit.app (Pro.seqHomColim M)).app L (Pro.seqStage M g)) =
        Pro.seqStage (M ⋙ F) (F.map g) :=
    (ConcreteCategory.congr_hom (congr_app (Pro.lanUnit_comp_lanSeqHomColimHom F M) L) _).trans
      (Pro.seqHomColimToComp_app_seqStage F M g)
  exact congrArg ((Pro.seqHomColimIso (M ⋙ F)).inv.app (F.obj L))
    ((congrArg ((Pro.lanSeqHomColimIso F M).hom.app (F.obj L)) h1).trans h2)

end Lan

end Sequences

variable (F : 𝒟 ⥤ 𝒟') [∀ A : 𝒟 ⥤ Type v, F.HasLeftKanExtension A]

/-- **`ProSeq.map F` applied to a morphism into a constant pro-object.** A morphism `g : P ⟶ L`
into the constant pro-object at `L` is an element of the functor of points of `P` at `L`; its
image under the unit of the left Kan extension along `F` is an element of the functor of points
of `ProSeq.map F P` at `F L`, that is, a morphism `ProSeq.map F P ⟶ F L`. -/
public def mapConst {P : ProSeq 𝒟} {L : 𝒟} (g : P ⟶ const.obj L) :
    (map F).obj P ⟶ const.obj (F.obj L) :=
  (homConstEquiv _ _).symm ((F.lanUnit.app P.points).app L (homConstEquiv P L g))

/-- The element of the functor of points that `ProSeq.mapConst F g` corresponds to. -/
public lemma homConstEquiv_mapConst {P : ProSeq 𝒟} {L : 𝒟} (g : P ⟶ const.obj L) :
    homConstEquiv _ _ (mapConst F g) =
      (F.lanUnit.app P.points).app L (homConstEquiv P L g) :=
  Equiv.apply_symm_apply _ _

end CategoryTheory.ProSeq

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable {X : Scheme.{u}} [IsNoetherian X]

/-- **The map `Rj_!(K|_U) ⟶ K` of [Stacks, Tag 0G4Y]** for an open `U` of a Noetherian scheme `X`,
`j : U ⟶ X` its inclusion: the canonical map `Rj'_!(K|_{U'}) ⟶ Rj_! K` of
`AlgebraicGeometry.extensionByZeroOpenCovariance` for the opens `U ⊆ X` (the inclusion `⊤ ⟶ X` of
the whole scheme playing the role of `j`), read through `(K|_X)|_U = K|_U` and through the
identification of `Rj_!` along `⊤ ⟶ X` with the identity, which is the morphism
`R(⊤ ⟶ X)_!(K|_⊤) ⟶ K` corresponding to the identity of `K|_⊤` under the adjointness of
[Stacks, Tag 0G4N]. -/
public def extensionByZeroCounit (U : X.Opens) (K : BoundedCoherentDerived X) :
    (extensionByZeroOpenImmersion U.ι).obj ((restrictBoundedCoherentLift U.ι).obj K) ⟶
      ProSeq.const.obj K :=
  (extensionByZeroOpenImmersion U.ι).map
      ((restrictBoundedCoherentLiftHomOfLEIso (le_top : U ≤ ⊤)).inv.app K) ≫
    (extensionByZeroOpenCovariance (le_top : U ≤ ⊤)).app
      ((restrictBoundedCoherentLift (⊤ : X.Opens).ι).obj K) ≫
    (extensionByZeroHomEquiv _ (DeligneSystem.values (⊤ : X.Opens).ι).toAssignment _ K).symm
      (𝟙 _)

/-- **The map `Rj_!(K|_U) ⟶ K` corresponds to the identity of `K|_U`** under the adjointness
`Hom_{Pro}(Rj_!(K|_U), K) = Hom_U(K|_U, K|_U)` of [Stacks, Tag 0G4N]. This determines it. -/
public lemma extensionByZeroHomEquiv_extensionByZeroCounit (U : X.Opens)
    (K : BoundedCoherentDerived X) :
    extensionByZeroHomEquiv _ (DeligneSystem.values U.ι).toAssignment _ K
        (extensionByZeroCounit U K) = 𝟙 _ := by
  refine (extensionByZeroHomEquiv_comp_map _ _ _ K _).trans ?_
  refine (congrArg (_ ≫ ·) (extensionByZeroOpenHomEquiv_covariance (le_top : U ≤ ⊤) _ K _)).trans ?_
  rw [Equiv.apply_symm_apply, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]

variable {Y : Scheme.{u}} [IsNoetherian Y] (p : X ⟶ Y) [IsProper p]

/-- **The map `Rg_!(K|_U) ⟶ Rp_* K` of [Stacks, Tag 0G56]**, for a proper `p : X ⟶ Y` to a
Noetherian scheme, an open `U ⊆ X` with inclusion `j`, `g = p ∘ j`, and `X` itself the
compactification of `U` over `Y` (so that `Rg_! = Rp_* ∘ Rj_!` is
`(CategoryTheory.CompactificationData.ofOpenImmersion j p).shriekImage`): the derived direct image
`Rp_*`, applied termwise, of the map `Rj_!(K|_U) ⟶ K` of [Stacks, Tag 0G4Y]
(`AlgebraicGeometry.extensionByZeroCounit`). This is the second construction of the source with
`X̄ = X`, the target `Rp_* ∘ R(id)_! K` being identified with `Rp_* K`. -/
public def lowerShriekToProperPushforward (U : X.Opens) (K : BoundedCoherentDerived X) :
    (CompactificationData.ofOpenImmersion U.ι p).shriekImage.obj
        ((restrictBoundedCoherentLift U.ι).obj K) ⟶
      ProSeq.const.obj ((properPushforwardBoundedCoherent p).obj K) :=
  ProSeq.mapConst (properPushforwardBoundedCoherent p) (extensionByZeroCounit U K)

end AlgebraicGeometry

end
