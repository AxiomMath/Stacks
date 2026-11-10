module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Colimits of sheaves of modules

Let `R` be a sheaf of rings on a site. The category of sheaves of `R`-modules has all
colimits, and they are computed by sheafifying a colimit of the underlying presheaves of
modules. When the site is the site of open subsets of a topological space, taking the stalk
at a point is a functor to modules over the stalk of `R`, and that functor preserves all
colimits.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.colimitSheafificationCocone`: the cocone obtained by
  sheafifying a cocone on the underlying diagram of presheaves of modules and transporting
  it along the counit of the sheafification adjunction.
* `AlgebraicGeometry.SheafOfModules.stalkObj`: the stalk of a sheaf of modules at a point,
  as a module over the stalk of the sheaf of rings.
* `AlgebraicGeometry.SheafOfModules.stalkMap`: the linear map on stalks induced by a
  morphism of sheaves of modules.
* `AlgebraicGeometry.SheafOfModules.stalkFunctor`: the stalk at a point, as a functor from
  sheaves of modules to modules over the stalk ring.

## Main results

* `AlgebraicGeometry.SheafOfModules.isColimit_colimitSheafificationCocone`: the sheafified
  cocone is colimiting whenever the presheaf cocone it comes from is.
* `AlgebraicGeometry.SheafOfModules.stalkFunctor_preservesColimits`: the stalk functor
  preserves colimits.
* `AlgebraicGeometry.SheafOfModules.isColimitMapCoconeOfSequence`: the same statement at the
  shape `ℕ`, namely that the stalk of an `ℕ`-indexed colimit is the colimit of the stalks.
* `AlgebraicGeometry.SheafOfModules.exists_stalkMap_eq` and
  `AlgebraicGeometry.SheafOfModules.exists_map_eq_zero_of_stalkMap_eq_zero`: the element-level
  form of that, the stalks of the stages being jointly surjective onto the stalk of the colimit
  and an element dying in the colimit being killed by a transition map.
* `SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf`
  gives all colimits in the category of sheaves of modules.

## Implementation notes

Mathlib proves the existence of colimits for a sheaf of rings on an arbitrary site whenever
the corresponding sheafification and presheaf colimits exist. These hypotheses are available
for the site of open subsets of a ringed space, so the existence statement specializes
directly and the existing instance is the declaration covering it.

The sheafification description of the colimit uses the counit of the sheafification
adjunction to identify every sheaf in the original diagram with the sheafification of its
underlying presheaf. Preservation of colimits by sheafification is recorded once, as
`preservesColimitsOfSize_sheafification`, and used both there and in the stalk argument.

The stalk module and its scalar action are the filtered-colimit construction from
`PresheafOfModules`. The map on a stalk is induced by the underlying map of presheaves of
abelian groups; compatibility with scalar multiplication is checked on germs, for which
`germ_hom_smul` restates Mathlib's germ-semilinearity in the explicitly bundled form the
rewrites need. Expressing the stalk result by `PreservesColimits` says precisely that every
canonical map from the colimit of the stalks to the stalk of the colimit is an isomorphism,
and retains its naturality in the diagram.

## References

* [Stacks Project, Tag 01AH](https://stacks.math.columbia.edu/tag/01AH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace Opposite

universe w' w v v' u' u

add_to_stacks 01AH "colimits_exist"
  SheafOfModules.instHasColimitsOfSizeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf

namespace AlgebraicGeometry.SheafOfModules

section Sheafification

variable {C : Type u'} [Category.{v', u'} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Sheafification of presheaves of modules is a left adjoint, hence preserves all
colimits. -/
theorem preservesColimitsOfSize_sheafification :
    PreservesColimitsOfSize.{w', w} (PresheafOfModules.sheafification (𝟙 R.obj)) :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).leftAdjoint_preservesColimits

variable {K : Type w} [Category.{w', w} K]

/-- The cocone on a diagram of sheaves obtained by sheafifying a cocone on its
underlying diagram of presheaves. -/
noncomputable def colimitSheafificationCocone
    (D : K ⥤ _root_.SheafOfModules.{v} R)
    (c : Cocone (D ⋙ _root_.SheafOfModules.forget R)) : Cocone D :=
  (Cocone.precompose
    (Functor.isoWhiskerLeft D
      (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).counit).symm).hom).obj
    ((PresheafOfModules.sheafification (𝟙 R.obj)).mapCocone c)

/-- Sheafification of a colimit of the underlying presheaves of modules is a
colimit of the original diagram of sheaves of modules. -/
@[stacks 01AH "colimits_sheafification"]
theorem isColimit_colimitSheafificationCocone
    (D : K ⥤ _root_.SheafOfModules.{v} R)
    (c : Cocone (D ⋙ _root_.SheafOfModules.forget R)) (hc : IsColimit c) :
    Nonempty (IsColimit (colimitSheafificationCocone R D c)) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let F := PresheafOfModules.sheafification (𝟙 R.obj)
  let _ : PreservesColimitsOfSize.{w', w} F :=
    preservesColimitsOfSize_sheafification R
  exact ⟨(IsColimit.precomposeHomEquiv
    (Functor.isoWhiskerLeft D (asIso adj.counit).symm)
    (F.mapCocone c)).symm (isColimitOfPreserves F hc)⟩

end Sheafification

section Stalks

/-- The forgetful functor from sheaves of modules over a sheaf of rings on a topological
space to sheaves of abelian groups preserves colimits. This is the open-cover-site case of
the general-site statement, at the unindexed `PreservesColimits` the stalk argument below
consumes; `TopCat.Sheaf` is a `def` rather than an abbreviation, so the elaborator will not
unify the two spellings of the sheaf type on its own. -/
private theorem toSheaf_preservesColimits {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    PreservesColimits (_root_.SheafOfModules.toSheaf.{u, u, u, u} O) := by
  let F := PresheafOfModules.sheafification (𝟙 O.obj)
  let adj : F ⊣ _ := PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)
  have hF : PreservesColimits F := preservesColimitsOfSize_sheafification O
  have hP : PreservesColimits (PresheafOfModules.toPresheaf O.obj) := inferInstance
  have hS : PreservesColimits
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).leftAdjoint_preservesColimits
  have hFT : PreservesColimits (F ⋙ _root_.SheafOfModules.toSheaf O) :=
    preservesColimits_of_natIso
      (PresheafOfModules.sheafificationCompToSheaf (𝟙 O.obj)).symm
  refine ⟨?_⟩
  intro J _
  refine ⟨?_⟩
  intro D
  refine ⟨?_⟩
  intro c hc
  let G := _root_.SheafOfModules.forget O ⋙ PresheafOfModules.restrictScalars (𝟙 O.obj)
  have e : (D ⋙ G) ⋙ F ≅ D :=
    NatIso.ofComponents (fun j => (asIso adj.counit).app (D.obj j)) (by
      intro i j f
      exact (asIso adj.counit).hom.naturality (D.map f))
  have h1 : PreservesColimit (D ⋙ G) F := hF.preservesColimitsOfShape.preservesColimit
  have h2 : PreservesColimit (D ⋙ G) (F ⋙ _root_.SheafOfModules.toSheaf O) :=
    hFT.preservesColimitsOfShape.preservesColimit
  have hpc : PreservesColimit ((D ⋙ G) ⋙ F) (_root_.SheafOfModules.toSheaf O) := by
    apply preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves F (colimit.isColimit (D ⋙ G)))
    exact isColimitOfPreserves (F ⋙ _root_.SheafOfModules.toSheaf O)
      (colimit.isColimit (D ⋙ G))
  have hD := preservesColimit_of_iso_diagram (_root_.SheafOfModules.toSheaf O) e
  exact ⟨isColimitOfPreserves (_root_.SheafOfModules.toSheaf O) hc⟩

variable {X : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)

/-- The stalk of a sheaf of `O`-modules at `x`, regarded as a module over the
stalk `O_x`. -/
noncomputable def stalkObj (M : _root_.SheafOfModules.{u} O) :
    ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x) :=
  ModuleCat.of (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X) M.val.presheaf x)

/-- Germ-semilinearity of the scalar action on a stalk, with the germ maps written as
bundled morphisms of abelian groups and of rings. -/
theorem germ_hom_smul (M : PresheafOfModules.{u} O.obj) (U : Opens X) (hx : x ∈ U)
    (r : O.obj.obj (op U)) (m : M.obj (op U)) :
    (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) M.presheaf U x hx).hom (r • m) =
      (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X) O.obj U x hx).hom r •
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X) M.presheaf U x hx).hom m :=
  PresheafOfModules.germ_ringCat_smul M x U hx r m

/-- The linear map on stalks induced by a morphism of sheaves of modules. -/
noncomputable def stalkMap {M N : _root_.SheafOfModules.{u} O} (f : M ⟶ N) :
    stalkObj O x M ⟶ stalkObj O x N :=
  ModuleCat.ofHom
    { toFun := fun s => (ConcreteCategory.hom
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf O.obj).map f.val))) s
      map_add' := by intro a b; exact map_add _ _ _
      map_smul' := by
        intro r s
        simp only [RingHom.id_apply]
        obtain ⟨Ur, hxr, a, ha⟩ := TopCat.Presheaf.exists_germ_eq O.obj r
        obtain ⟨Um, hxm, m, hm⟩ := TopCat.Presheaf.exists_germ_eq M.val.presheaf s
        let U : Opens X := Ur ⊓ Um
        have hxU : x ∈ U := ⟨hxr, hxm⟩
        let iUr : U ⟶ Ur := homOfLE inf_le_left
        let iUm : U ⟶ Um := homOfLE inf_le_right
        let a' : O.obj.obj (op U) := (O.obj.map iUr.op).hom a
        let m' : M.val.obj (op U) := (M.val.presheaf.map iUm.op).hom m
        have hga : (TopCat.Presheaf.germ (C := RingCat.{u}) (X := X)
            O.obj U x hxU).hom a' = r := by
          rw [show a' = (O.obj.map iUr.op).hom a from rfl,
            TopCat.Presheaf.germ_res_apply]
          exact ha
        have hgm : (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
            M.val.presheaf U x hxU).hom m' = s := by
          rw [show m' = (M.val.presheaf.map iUm.op).hom m from rfl,
            TopCat.Presheaf.germ_res_apply]
          exact hm
        let Φ := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf O.obj).map f.val)
        have eM : r • s = (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
            M.val.presheaf U x hxU).hom (a' • m') := by
          rw [← hga, ← hgm]
          exact (germ_hom_smul O x M.val U hxU a' m').symm
        have nat : ∀ t : M.val.obj (op U),
            Φ.hom ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
              M.val.presheaf U x hxU).hom t) =
              (TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (X := X)
                N.val.presheaf U x hxU).hom (f.val.app (op U) t) := by
          intro t
          exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hxU
            ((PresheafOfModules.toPresheaf O.obj).map f.val) t
        have lin : f.val.app (op U) (a' • m') = a' • f.val.app (op U) m' :=
          map_smul _ _ _
        have eN := germ_hom_smul O x N.val U hxU a' (f.val.app (op U) m')
        rw [eM, nat, lin, eN, hga, ← nat, hgm] }

/-- Taking the stalk at `x` as a module over the stalk of the sheaf of rings. -/
noncomputable def stalkFunctor :
    CategoryTheory.Functor (_root_.SheafOfModules.{u} O)
      (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)) where
  obj := stalkObj O x
  map := stalkMap O x
  map_id M := by
    ext s
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf O.obj).map (𝟙 M.val))).hom s = s
    simp
    rfl
  map_comp f g := by
    ext s
    change ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf O.obj).map (f.val ≫ g.val))).hom s = _
    simp [stalkMap]
    rfl

/-- The canonical map from the colimit of the stalks of a diagram of sheaves
of modules to the stalk of its colimit is an isomorphism. It is the inverse of
`CategoryTheory.Limits.preservesColimitIso`; its compatibility with the colimit
inclusions is `CategoryTheory.Limits.ι_preservesColimitIso_inv`. -/
@[stacks 01AH "colimits_stalks", instance, ega "0 4.3.2" "special case"]
lemma stalkFunctor_preservesColimits : PreservesColimits (stalkFunctor O x) := by
  let G := forget₂ (ModuleCat.{u} (TopCat.Presheaf.stalk
    (C := RingCat.{u}) (X := X) O.obj x)) AddCommGrpCat.{u}
  have h : PreservesColimits (stalkFunctor O x ⋙ G) := by
    change PreservesColimits ((_root_.SheafOfModules.toSheaf O ⋙
      TopCat.Sheaf.forget AddCommGrpCat.{u} X) ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
    have hM : PreservesColimits (_root_.SheafOfModules.toSheaf.{u, u, u, u} O) :=
      toSheaf_preservesColimits O
    have hs' : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
        (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := by infer_instance
    change PreservesColimits (_root_.SheafOfModules.toSheaf O ⋙
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x))
    exact @comp_preservesColimits.{u, u, u, u, u, u + 1, u + 1, u + 1}
      _ _ _ _ _ _ (_root_.SheafOfModules.toSheaf O)
      (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) hM hs'
  have hr : ReflectsColimits G := ⟨fun {J} _ => inferInstance⟩
  exact preservesColimits_of_reflects_of_preserves (stalkFunctor O x) G

/-! ### `ℕ`-indexed colimits of stalks -/

section Sequence

variable {D : CategoryTheory.Functor ℕ (_root_.SheafOfModules.{u} O)}

/-- **The stalk of an `ℕ`-indexed colimit is the `ℕ`-indexed colimit of the stalks.**  This is
`stalkFunctor_preservesColimits`, that is [Stacks, Tag 01AH], specialized to the shape `ℕ`:
`CategoryTheory.Limits.preservesColimitsOfSize_shrink` brings the statement down from shapes in
`Type u` to `ℕ`, which lives in `Type 0`, and nothing is narrowed because `max 0 u = u`. -/
@[ega "0 4.3.2" "special case"]
noncomputable def isColimitMapCoconeOfSequence {c : Cocone D} (hc : IsColimit c) :
    IsColimit ((stalkFunctor O x).mapCocone c) := by
  letI : PreservesColimits (stalkFunctor O x) := stalkFunctor_preservesColimits O x
  letI : PreservesColimitsOfSize.{0, 0} (stalkFunctor O x) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  exact isColimitOfPreserves _ hc

/-- The forgetful functor to types preserves the colimit of an `ℕ`-indexed diagram of modules
over the stalk ring: `ℕ` is filtered, and the forgetful functor from modules preserves filtered
colimits of shapes in `Type u`, hence — `ℕ` being in `Type 0` — of shape `ℕ`. -/
instance preservesColimit_comp_stalkFunctor_forget :
    PreservesColimit (D ⋙ stalkFunctor O x)
      (forget (ModuleCat.{u} (TopCat.Presheaf.stalk
        (C := RingCat.{u}) (X := X) O.obj x))) := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u}
      (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, 0, 0} _
  infer_instance

/-- **Joint surjectivity of the stalk maps into the stalk of an `ℕ`-indexed colimit.**  Every
element of the stalk of the colimit comes from the stalk of one of the stages. -/
theorem exists_stalkMap_eq {c : Cocone D} (hc : IsColimit c) (a : stalkObj O x c.pt) :
    ∃ (n : ℕ) (m : stalkObj O x (D.obj n)), stalkMap O x (c.ι.app n) m = a :=
  Concrete.isColimit_exists_rep _ (isColimitMapCoconeOfSequence O x hc) a

/-- **An element of a stage killed in the stalk of the colimit is killed by a transition map.**
The colimit being filtered, two elements with the same image agree after a transition; applied
to `m` and `0` this says that some `D.map (n ⟶ n + k)` kills `m`. -/
theorem exists_map_eq_zero_of_stalkMap_eq_zero {c : Cocone D} (hc : IsColimit c) (n : ℕ)
    (m : stalkObj O x (D.obj n)) (h : stalkMap O x (c.ι.app n) m = 0) :
    ∃ k : ℕ, stalkMap O x (D.map (homOfLE (Nat.le_add_right n k))) m = 0 := by
  obtain ⟨j, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq.{u} (D ⋙ stalkFunctor O x)
    (isColimitMapCoconeOfSequence O x hc) m (0 : (D ⋙ stalkFunctor O x).obj n)
    (h.trans (map_zero _).symm)
  obtain ⟨k, rfl⟩ := Nat.le.dest (leOfHom f)
  obtain rfl : f = homOfLE (Nat.le_add_right n k) := Subsingleton.elim _ _
  exact ⟨k, hfg.trans (map_zero _)⟩

end Sequence

end Stalks

end AlgebraicGeometry.SheafOfModules

