module

public import StacksFrontier.Topology.Sheaves.Glueing.Sheaf
public import StacksFrontier.Topology.Sheaves.Glueing.MapGluing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheaves of sets are the same thing as glueing data (Stacks 00AN)

Let `X` be a topological space and let `X = ⋃ i, U i` be an open covering. Restricting a sheaf of
sets `F` on `X` to each `U i`, and taking the comparison isomorphisms over the overlaps to be the
identity, produces a glueing datum in the sense of `TopCat.Sheaf.GlueData`. This is a functor, and
Stacks 00AN asserts that it is an equivalence of categories.

## Main definitions

* `TopCat.Sheaf.GlueData.Hom`: a morphism of glueing data, i.e. a family of morphisms of the local
  sheaves commuting with the comparison isomorphisms.
* `TopCat.Sheaf.glueDataFunctor`: the functor `Sh(X) ⥤ GlueData X U`.

## Main results

* `TopCat.Sheaf.sheafEquivGlueData`: **Stacks 00AN**, the equivalence between sheaves of sets on
  `X` and glueing data with respect to `X = ⋃ i, U i`.

Following the proof in Stacks 00AN, the functor is fully faithful by Stacks 04TN
(`TopCat.Sheaf.existsUnique_hom_of_localHom`) and essentially surjective by Stacks 00AL
(`TopCat.Sheaf.GlueData.glued` together with `TopCat.Sheaf.GlueData.sectionsEquiv`).

## Implementation notes

Only the statement for sheaves of *sets* is formalised here. Stacks 00AN also asserts the analogous
equivalences for abelian sheaves, for sheaves of algebraic structures and for sheaves of
`O`-modules; those are not covered by this file.

The comparison isomorphisms of the glueing datum attached to a sheaf `F` are literally the
identity: in the encoding of `TopCat.Sheaf.LocalPresheaf`, the sections of `F|_{U i}` over an open
`V` of `X` with `V ≤ U i` are the sections `F(V)`, with no dependence on `i` whatsoever. This is
what makes the `U i ⊓ U j` bookkeeping of Stacks 00AN disappear.

Essential surjectivity does not need the covering hypothesis, and neither does the functor itself;
fullness and faithfulness do, and that is where Stacks 04TN enters.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace TopCat.Sheaf

variable {X : TopCat.{u}} {ι : Type u} {U : ι → Opens X}

/-! ### The category of glueing data -/

/-- A morphism of glueing data: a morphism of the local sheaves over each `U i`, commuting with the
comparison isomorphisms over the overlaps. -/
@[ext]
structure GlueData.Hom (D E : GlueData X U) where
  /-- The morphism of local sheaves on `U i`. -/
  hom : ∀ i, LocalPresheaf.Hom (D.sheaf i) (E.sheaf i)
  /-- Compatibility with the comparison isomorphisms. -/
  trans_app : ∀ (i j : ι) {V : Opens X} (hi : V ≤ U i) (hj : V ≤ U j)
      (s : (D.sheaf i).obj V hi),
      (hom j).app V hj (D.trans i j hi hj s) = E.trans i j hi hj ((hom i).app V hi s)

/-- Glueing data with respect to a fixed family of opens form a category. -/
instance : Category.{u} (GlueData X U) where
  Hom D E := GlueData.Hom D E
  id D := ⟨fun i => LocalPresheaf.Hom.id (D.sheaf i), by intros; rfl⟩
  comp f g := ⟨fun i => (f.hom i).comp (g.hom i), by
    intro i j V hi hj s
    rw [LocalPresheaf.Hom.comp_app, LocalPresheaf.Hom.comp_app, Function.comp_apply,
      Function.comp_apply, f.trans_app, g.trans_app]⟩
  id_comp _ := GlueData.Hom.ext rfl
  comp_id _ := GlueData.Hom.ext rfl
  assoc _ _ _ := GlueData.Hom.ext rfl

/-! ### The functor from sheaves to glueing data -/

/-- The functor sending a sheaf of sets on `X` to its glueing data with respect to the family `U`.
The comparison isomorphisms of the resulting glueing datum are the identity. -/
def glueDataFunctor (U : ι → Opens X) : X.Sheaf (Type u) ⥤ GlueData X U where
  obj F :=
    { sheaf := fun i => TopCat.Presheaf.toLocalPresheaf F.1 (U i)
      isSheaf := fun i => TopCat.Presheaf.isSheaf_toLocalPresheaf F.2 (U i)
      trans := fun _ _ _ _ _ => Equiv.refl _
      trans_map := by intros; rfl
      trans_trans := by intros; rfl }
  map ψ :=
    { hom := fun _ =>
        { app := fun V _ s => ψ.1.app (op V) s
          naturality := fun hWV s => NatTrans.naturality_apply ψ.1 (homOfLE hWV).op s }
      trans_app := by intros; rfl }
  map_id _ := GlueData.Hom.ext (funext fun _ => LocalPresheaf.Hom.ext rfl)
  map_comp _ _ := GlueData.Hom.ext (funext fun _ => LocalPresheaf.Hom.ext rfl)

/-- The local sheaf maps underlying a morphism of the glueing data attached to two sheaves, viewed
as `TopCat.Sheaf.LocalSheafHom`s so that Stacks 04TN applies to them. -/
private def localSheafHomOfHom {F G : X.Sheaf (Type u)}
    (f : (glueDataFunctor U).obj F ⟶ (glueDataFunctor U).obj G) (i : ι) :
    LocalSheafHom F G (U i) where
  app V hV := (f.hom i).app V hV
  naturality V W hV hW k s := by
    rw [show k = homOfLE (Quiver.Hom.le k) from Subsingleton.elim _ _]
    exact ((f.hom i).naturality (Quiver.Hom.le k) s).symm

/-- The local sheaf maps of `localSheafHomOfHom` agree on the overlaps, which is the hypothesis of
Stacks 04TN: this is exactly the compatibility of `f` with the comparison isomorphisms, which are
the identity here. -/
private theorem localSheafHomOfHom_agree {F G : X.Sheaf (Type u)}
    (f : (glueDataFunctor U).obj F ⟶ (glueDataFunctor U).obj G) (i j : ι) (V : Opens X)
    (hVi : V ≤ U i) (hVj : V ≤ U j) :
    (localSheafHomOfHom f i).app V hVi = (localSheafHomOfHom f j).app V hVj :=
  funext fun s => (f.trans_app i j hVi hVj s).symm

/-- The glueing data functor is faithful: two morphisms of sheaves that agree on every open
contained in some `U i` are equal, by the uniqueness half of Stacks 04TN. -/
theorem glueDataFunctor_faithful (hU : ⨆ i, U i = ⊤) : (glueDataFunctor U).Faithful where
  map_injective {F} {G} {ψ} {_ψ'} h :=
    (existsUnique_hom_of_localHom U hU F G (localSheafHomOfHom ((glueDataFunctor U).map ψ))
        (localSheafHomOfHom_agree _)).unique
      (fun _ _ _ => rfl) fun i V hV => congrArg (fun m => (m.hom i).app V hV) h.symm

/-- The glueing data functor is full: a family of maps on the `U i` agreeing on the overlaps glues
to a morphism of sheaves by Stacks 04TN. -/
theorem glueDataFunctor_full (hU : ⨆ i, U i = ⊤) : (glueDataFunctor U).Full where
  map_surjective {F} {G} f := by
    obtain ⟨ψ, hψ, -⟩ :=
      existsUnique_hom_of_localHom U hU F G (localSheafHomOfHom f) (localSheafHomOfHom_agree f)
    exact ⟨ψ, GlueData.Hom.ext (funext fun i => LocalPresheaf.Hom.ext
      (funext fun V => funext fun hV => hψ i V hV))⟩

/-! ### The quasi-inverse -/

/-- The inverse of the comparison isomorphism `φ i` of Stacks 00AL commutes with restriction. -/
theorem GlueData.sectionsEquiv_symm_map (D : GlueData X U) (i : ι) {V W : Opens X} (hV : V ≤ U i)
    (hWV : W ≤ V) (t : (D.sheaf i).obj V hV) :
    (D.sectionsEquiv i (hWV.trans hV)).symm ((D.sheaf i).map hWV t)
      = D.sectionsMap hWV ((D.sectionsEquiv i hV).symm t) :=
  (D.sectionsEquiv i (hWV.trans hV)).injective <| by
    rw [Equiv.apply_symm_apply, D.sectionsEquiv_map, Equiv.apply_symm_apply]

/-- The inverse form of the commuting diagram of Stacks 00AL: the inverses of the comparison
isomorphisms `φ i` and `φ j` differ by `φ i j`. -/
theorem GlueData.trans_sectionsEquiv_symm (D : GlueData X U) (i j : ι) {V : Opens X} (hi : V ≤ U i)
    (hj : V ≤ U j) (t : (D.sheaf i).obj V hi) :
    (D.sectionsEquiv j hj).symm (D.trans i j hi hj t) = (D.sectionsEquiv i hi).symm t :=
  (D.sectionsEquiv j hj).injective <| by
    rw [Equiv.apply_symm_apply, ← D.trans_sectionsEquiv i j hi hj, Equiv.apply_symm_apply]

/-- The glueing data of the sheaf glued from `D` is isomorphic to `D`, via the comparison
isomorphisms of Stacks 00AL. -/
def GlueData.gluedIso (D : GlueData X U) : (glueDataFunctor U).obj D.glued ≅ D where
  hom :=
    { hom := fun i =>
        { app := fun _ hV => D.sectionsEquiv i hV
          naturality := by
            intro V W hV hWV s
            exact D.sectionsEquiv_map i hV hWV s }
      trans_app := by
        intro i j V hi hj s
        exact (D.trans_sectionsEquiv i j hi hj s).symm }
  inv :=
    { hom := fun i =>
        { app := fun _ hV => (D.sectionsEquiv i hV).symm
          naturality := by
            intro V W hV hWV s
            exact D.sectionsEquiv_symm_map i hV hWV s }
      trans_app := by
        intro i j V hi hj s
        exact D.trans_sectionsEquiv_symm i j hi hj s }
  hom_inv_id := GlueData.Hom.ext (funext fun i => LocalPresheaf.Hom.ext (funext fun _ =>
    funext fun hV => funext fun s => (D.sectionsEquiv i hV).symm_apply_apply s))
  inv_hom_id := GlueData.Hom.ext (funext fun i => LocalPresheaf.Hom.ext (funext fun _ =>
    funext fun hV => funext fun s => (D.sectionsEquiv i hV).apply_symm_apply s))

/-- The glueing data functor is essentially surjective: every glueing datum is the glueing data of
the sheaf glued from it (Stacks 00AL). -/
theorem glueDataFunctor_essSurj : (glueDataFunctor U).EssSurj where
  mem_essImage D := ⟨D.glued, ⟨D.gluedIso⟩⟩

/-- **Stacks 00AN.** For an open covering `X = ⋃ i, U i`, restriction to the members of the
covering is an equivalence between the category of sheaves of sets on `X` and the category of
glueing data with respect to the covering. -/
@[stacks 00AN, ega "0 3.3.1" "special case"]
noncomputable def sheafEquivGlueData (hU : ⨆ i, U i = ⊤) : X.Sheaf (Type u) ≌ GlueData X U :=
  haveI := glueDataFunctor_faithful hU
  haveI := glueDataFunctor_full hU
  haveI := glueDataFunctor_essSurj (U := U)
  haveI : (glueDataFunctor U).IsEquivalence := {}
  (glueDataFunctor U).asEquivalence

end TopCat.Sheaf
