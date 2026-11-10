module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.SetTheory.Ordinal.Basic

/-!
# The successor step of the sheafification tower

Let `C` be a site, `i = sheafToPresheaf J Ab : Ab(C) ⥤ PAb(C)` the forgetful functor and
`(-)^# = presheafToSheaf J Ab : PAb(C) ⥤ Ab(C)` sheafification. Given a functor
`Jemb : PAb(C) ⥤ PAb(C)` with a natural transformation `Jemb_emb : 𝟭 ⟶ Jemb`, set
`J_1(H) = (Jemb (i H))^#` for an abelian sheaf `H`, with the canonical map `c : H ⟶ J_1(H)`
obtained by sheafifying `i H ⟶ Jemb (i H)` and using the counit isomorphism `(i H)^# ≅ H`.

A `JSystem` is an ordinal-indexed tower `β ↦ J_β(F)` with `J_0(F) = F`,
`J_{α+1}(F) = J_1(J_α(F))`, the canonical map `c` as transition map `J_α(F) ⟶ J_{α+1}(F)`,
the colimit of the `J_α(F)`, `α < β`, at a limit ordinal `β`, and monomorphic transition maps.

## Main definitions

* `Stacks.Injectives.SheafificationTower.J1`: the sheaf `J_1(H) = (Jemb (i H))^#`.
* `Stacks.Injectives.SheafificationTower.cmap`: the canonical map `c : H ⟶ J_1(H)`.
* `Stacks.Injectives.SheafificationTower.JSystem`: an ordinal-indexed tower `β ↦ J_β(F)` with
  the properties above.

## Main results

* `Stacks.Injectives.SheafificationTower.main_theorem_01dm`: if every `Jemb B` is injective,
  then for a monomorphism `ι : G₁ ⟶ G₂` of abelian sheaves every `f : G₁ ⟶ J_α(F)` extends to
  some `g : G₂ ⟶ J_{α+1}(F)` with `ι ≫ g = f ≫ c`.
* `Stacks.Injectives.SheafificationTower.cmap_mono`: if every component of `Jemb_emb` is a
  monomorphism, then so is `c`.

## Implementation notes

A `JSystem` records `J_0(F) = F` and `J_{α+1}(F) = J_1(J_α(F))` as equalities of abelian
sheaves, which the transfinite construction only realizes up to isomorphism. The corresponding
statement for the constructed tower is
`Stacks.Injectives.SheafificationTowerFactorization.exists_extension_towerIota_succ`.

## References

* [Stacks Project, Tag 01DM](https://stacks.math.columbia.edu/tag/01DM)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace Stacks.Injectives.SheafificationTower

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The successor step `J_1` applied to an abelian sheaf `H`: `J_1(H) = (Jemb (i H))^#`. -/
noncomputable def J1 (Jemb : (Cᵒᵖ ⥤ Ab.{u}) ⥤ (Cᵒᵖ ⥤ Ab.{u})) (H : Sheaf J Ab.{u}) :
    Sheaf J Ab.{u} :=
  (presheafToSheaf J Ab.{u}).obj (Jemb.obj ((sheafToPresheaf J Ab.{u}).obj H))

/-- The canonical map `c : H → J_1(H)`, obtained by sheafifying the embedding
`i H → Jemb (i H)` and using the counit isomorphism `(i H)^# ≅ H`. -/
noncomputable def cmap (Jemb : (Cᵒᵖ ⥤ Ab.{u}) ⥤ (Cᵒᵖ ⥤ Ab.{u}))
    (Jemb_emb : (𝟭 (Cᵒᵖ ⥤ Ab.{u})) ⟶ Jemb) (H : Sheaf J Ab.{u}) : H ⟶ J1 J Jemb H :=
  (asIso ((sheafificationAdjunction J Ab.{u}).counit.app H)).inv ≫
    (presheafToSheaf J Ab.{u}).map (Jemb_emb.app ((sheafToPresheaf J Ab.{u}).obj H))

/-- The diagram `α ↦ J_α(F)` for `α < β`, restricted from a full ordinal-indexed
diagram `D`. -/
def belowDiag (β : Ordinal.{u}) (D : Ordinal.{u} ⥤ Sheaf J Ab.{u}) :
    {α : Ordinal.{u} // α < β} ⥤ Sheaf J Ab.{u} :=
  (Monotone.functor (f := (Subtype.val : {α : Ordinal.{u} // α < β} → Ordinal.{u}))
    (fun _ _ h => h)) ⋙ D

/-- The canonical cocone over the `J_α(F)`, `α < β`, with apex `J_β(F)`, whose legs
are the canonical transition maps. -/
def belowCocone (β : Ordinal.{u}) (D : Ordinal.{u} ⥤ Sheaf J Ab.{u}) :
    Cocone (belowDiag J β D) where
  pt := D.obj β
  ι :=
    { app := fun α => D.map (homOfLE (le_of_lt α.property))
      naturality := by
        intro α α' h
        simp only [belowDiag, Functor.comp_obj, Functor.const_obj_obj, Functor.comp_map,
          Functor.const_obj_map, Category.comp_id]
        rw [← D.map_comp]
        rfl }

/-- An ordinal-indexed tower `β ↦ J_β(F)`, packaged as data. `diag` is the functor
`β ↦ J_β(F)` from the (linearly ordered) category of ordinals, so it supplies the canonical
transition maps `J_α(F) ⟶ J_β(F)` for `α ≤ β` together with functoriality. The other fields
record:
* `zero` : `J_0(F) = F`;
* `succ_obj`/`succ_map` : `J_{α+1}(F) = J_1(J_α(F))` with the canonical map being
  `cmap` (up to that identification);
* `isColimit` : at a limit ordinal `β`, `J_β(F)` is the colimit of the `J_α(F)` for
  `α < β` (directed colimit);
* `mono` : every canonical transition map `J_α(F) ⟶ J_β(F)` is a monomorphism. -/
structure JSystem (Jemb : (Cᵒᵖ ⥤ Ab.{u}) ⥤ (Cᵒᵖ ⥤ Ab.{u}))
    (Jemb_emb : (𝟭 (Cᵒᵖ ⥤ Ab.{u})) ⟶ Jemb) (F : Sheaf J Ab.{u}) where
  /-- `β ↦ J_β(F)` as a functor on the order category of ordinals. -/
  diag : Ordinal.{u} ⥤ Sheaf J Ab.{u}
  /-- `J_0(F) = F`. -/
  zero : diag.obj 0 = F
  /-- `J_{α+1}(F) = J_1(J_α(F))`. -/
  succ_obj : ∀ α : Ordinal.{u}, diag.obj (Order.succ α) = J1 J Jemb (diag.obj α)
  /-- The canonical map `J_α(F) ⟶ J_{α+1}(F)` is `cmap` (up to the identification
  `succ_obj`). -/
  succ_map : ∀ α : Ordinal.{u},
    diag.map (homOfLE (Order.le_succ α)) =
      cmap J Jemb Jemb_emb (diag.obj α) ≫ eqToHom (succ_obj α).symm
  /-- At a limit ordinal `β`, `J_β(F)` is the directed colimit of `J_α(F)`, `α < β`. -/
  isColimit : ∀ β : Ordinal.{u}, Order.IsSuccLimit β →
    Nonempty (IsColimit (belowCocone J β diag))
  /-- Every canonical transition map is a monomorphism. -/
  mono : ∀ {α β : Ordinal.{u}} (h : α ≤ β), Mono (diag.map (homOfLE h))

/-- Let `C` be a site, `F` an abelian sheaf, `α` an ordinal, and `S` a `JSystem` for `F`, with
`J_α(F) = S.diag.obj α`, `J_{α+1}(F) = S.diag.obj (α + 1)` and canonical map
`c = S.diag.map : J_α(F) ⟶ J_{α+1}(F)`, every `Jemb B` being injective. If `ι : G₁ → G₂` is a
monomorphism of abelian sheaves and `f : G₁ → J_α(F)` is a morphism, then there exists a
morphism `g : G₂ → J_{α+1}(F)` such that `ι ≫ g = f ≫ c`. -/
theorem main_theorem_01dm
    (Jemb : (Cᵒᵖ ⥤ Ab.{u}) ⥤ (Cᵒᵖ ⥤ Ab.{u}))
    (Jemb_emb : (𝟭 (Cᵒᵖ ⥤ Ab.{u})) ⟶ Jemb)
    (Jemb_inj : ∀ B : Cᵒᵖ ⥤ Ab.{u}, Injective (Jemb.obj B))
    (F : Sheaf J Ab.{u}) (S : JSystem J Jemb Jemb_emb F) (α : Ordinal.{u})
    {G₁ G₂ : Sheaf J Ab.{u}} (ι : G₁ ⟶ G₂) [Mono ι]
    (f : G₁ ⟶ S.diag.obj α) :
    ∃ g : G₂ ⟶ S.diag.obj (Order.succ α),
      ι ≫ g = f ≫ S.diag.map (homOfLE (Order.le_succ α)) := by
  set i := sheafToPresheaf J Ab.{u}
  set sh := presheafToSheaf J Ab.{u}
  set adj := sheafificationAdjunction J Ab.{u}
  let hpre : i.obj G₁ ⟶ Jemb.obj (i.obj (S.diag.obj α)) :=
    i.map f ≫ Jemb_emb.app (i.obj (S.diag.obj α))
  have : Injective (Jemb.obj (i.obj (S.diag.obj α))) := Jemb_inj _
  have : Mono (i.map ι) := (inferInstance : Mono ((sheafToPresheaf J Ab.{u}).map ι))
  let k : i.obj G₂ ⟶ Jemb.obj (i.obj (S.diag.obj α)) := Injective.factorThru hpre (i.map ι)
  have hk : i.map ι ≫ k = hpre := Injective.comp_factorThru _ _
  let g₀ : G₂ ⟶ sh.obj (Jemb.obj (i.obj (S.diag.obj α))) :=
    (asIso (adj.counit.app G₂)).inv ≫ sh.map k
  refine ⟨g₀ ≫ eqToHom (S.succ_obj α).symm, ?_⟩
  have nat : ∀ {X Y : Sheaf J Ab.{u}} (φ : X ⟶ Y),
      φ ≫ (asIso (adj.counit.app Y)).inv
        = (asIso (adj.counit.app X)).inv ≫ sh.map (i.map φ) := by
    intro X Y φ
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    simp only [asIso_hom]
    exact (adj.counit_naturality φ).symm
  have key : ι ≫ g₀ = f ≫ cmap J Jemb Jemb_emb (S.diag.obj α) := by
    change ι ≫ ((asIso (adj.counit.app G₂)).inv ≫ sh.map k)
        = f ≫ cmap J Jemb Jemb_emb (S.diag.obj α)
    simp only [cmap]
    rw [← Category.assoc, nat ι, Category.assoc, ← sh.map_comp, hk]
    change (asIso (adj.counit.app G₁)).inv ≫
        sh.map (i.map f ≫ Jemb_emb.app (i.obj (S.diag.obj α)))
        = f ≫ (asIso (adj.counit.app (S.diag.obj α))).inv ≫
            sh.map (Jemb_emb.app (i.obj (S.diag.obj α)))
    rw [Functor.map_comp, ← Category.assoc, ← nat f, Category.assoc]
  calc ι ≫ g₀ ≫ eqToHom (S.succ_obj α).symm
      = (ι ≫ g₀) ≫ eqToHom (S.succ_obj α).symm := (Category.assoc _ _ _).symm
    _ = (f ≫ cmap J Jemb Jemb_emb (S.diag.obj α)) ≫ eqToHom (S.succ_obj α).symm :=
          congrArg (· ≫ eqToHom (S.succ_obj α).symm) key
    _ = f ≫ cmap J Jemb Jemb_emb (S.diag.obj α) ≫ eqToHom (S.succ_obj α).symm :=
          Category.assoc _ _ _
    _ = f ≫ S.diag.map (homOfLE (Order.le_succ α)) := by rw [S.succ_map α]

/-- If every component of `Jemb_emb` is a monomorphism, then the canonical map
`c : H ⟶ J_1(H)` is a monomorphism. -/
theorem cmap_mono
    (Jemb : (Cᵒᵖ ⥤ Ab.{u}) ⥤ (Cᵒᵖ ⥤ Ab.{u}))
    (Jemb_emb : (𝟭 (Cᵒᵖ ⥤ Ab.{u})) ⟶ Jemb)
    (Jemb_emb_mono : ∀ B : Cᵒᵖ ⥤ Ab.{u}, Mono (Jemb_emb.app B))
    (H : Sheaf J Ab.{u}) :
    Mono (cmap J Jemb Jemb_emb H) := by
  have : Mono (Jemb_emb.app ((sheafToPresheaf J Ab.{u}).obj H)) := Jemb_emb_mono _
  have h2 : Mono ((presheafToSheaf J Ab.{u}).map
      (Jemb_emb.app ((sheafToPresheaf J Ab.{u}).obj H))) :=
    preserves_mono_of_preservesLimit _ _
  have h1 : Mono (asIso ((sheafificationAdjunction J Ab.{u}).counit.app H)).inv := inferInstance
  unfold cmap
  exact @mono_comp _ _ _ _ _ _ h1 _ h2

end Stacks.Injectives.SheafificationTower
