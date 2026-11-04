module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.ModObj
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SectionEquivGroupRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.SliceTorsorActions
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.TorsorClasses

/-!
# Inverse images of sheaves of groups and of torsors

Let `(C, J)` and `(D, K)` be sites and let `L : Sh(C) ⥤ Sh(D)` be a functor between the
categories of sheaves of sets which preserves finite products, for instance the inverse image
functor of a morphism of sites. A sheaf of groups on `C` is a group object of `Sh(C)`, and a
pseudo-torsor under it is a module object whose shear map `(g, s) ↦ (g · s, s)` is an
isomorphism; both notions are preserved by `L`. So `L` carries a sheaf of groups `G` to a sheaf
of groups `L G`, and a pseudo-`G`-torsor `F` to a pseudo-`L G`-torsor `L F`. If `L` moreover
preserves epimorphisms, as a left adjoint does, it preserves local nonemptiness, hence carries
torsors to torsors and induces a map `H¹(C, G) → H¹(D, L G)` on isomorphism classes of torsors.

This map is injective when `L` is fully faithful. Suppose that `L` is left adjoint to the
restriction `u_*` along a continuous functor `u : C ⥤ D` and that the unit `G ⟶ u_* L G` is an
isomorphism. If an `L G`-torsor `T` has sections locally on the image of `u`, then its
restriction `u_* T` is a `G`-torsor, and the counit `L u_* T ⟶ T` is a morphism of torsors;
hence the class of `T` lies in the image. This is the argument of Stacks 099X once étale local
triviality is known.

## Main definitions

* `SheafOfGroups.sheaf`, `PseudoTorsor.sheaf`: the underlying sheaves of sets, with their group
  and module object structures.
* `SheafOfGroups.ofGrpObj`, `PseudoTorsor.ofModObj`: a group object of sheaves of sets is a sheaf
  of groups, and a module object over it with invertible shear map is a pseudo-torsor.
* `SheafOfGroups.map`, `PseudoTorsor.map`, `PseudoTorsor.Hom.map`: the images under `L`.
* `SheafOfGroups.TorsorClasses.map`: the induced map `H¹(C, G) → H¹(D, L G)`.
* `PseudoTorsor.pushforward`: the restriction `u_* T` of an `L G`-pseudo-torsor, as a
  pseudo-`G`-torsor through the unit of the adjunction.

## Main results

* `PseudoTorsor.isTorsor_iff_isLocallySurjective`: a pseudo-torsor is a torsor exactly when its
  map to the final sheaf is locally surjective.
* `PseudoTorsor.isTorsor_map`: `L` carries torsors to torsors.
* `SheafOfGroups.TorsorClasses.map_injective`: the map on `H¹` is injective for fully faithful
  `L`.
* `SheafOfGroups.TorsorClasses.map_bijective_of_adjunction`: the map on `H¹` is bijective if `L`
  is left adjoint to `u_*` with invertible unit and every `L G`-torsor has sections locally on
  the image of `u`.

## References

* [Stacks Project, Tag 03AH](https://stacks.math.columbia.edu/tag/03AH)
* [Stacks Project, Tag 099X](https://stacks.math.columbia.edu/tag/099X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory CartesianMonoidalCategory
  MonObj

universe w v u v' u'

attribute [local instance high] SemiCartesianMonoidalCategory.toMonoidalCategory
attribute [local instance high] MonoidalCategory.toMonoidalCategoryStruct
attribute [local instance] Functor.Monoidal.ofChosenFiniteProducts

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-! ### Sheaves of groups as group objects of sheaves of sets -/

namespace SheafOfGroups

/-- The underlying sheaf of sets of a sheaf of groups. -/
abbrev sheaf (G : SheafOfGroups.{w} J) : Sheaf J (Type w) :=
  ⟨G.presheaf, G.isSheaf⟩

/-- A sheaf of groups is a group object of the category of sheaves of sets: the cartesian
monoidal structure of sheaves of sets is computed section-wise. -/
instance grpObjSheaf (G : SheafOfGroups.{w} J) : GrpObj G.sheaf where
  one := ⟨({
      app := fun U => ↾fun _ : (𝟙_ (Cᵒᵖ ⥤ Type w)).obj U => (1 : G.presheaf.obj U)
      naturality := fun _ _ f => by ext _; exact (SheafOfGroups.map_one (G := G) f).symm } :
    𝟙_ (Cᵒᵖ ⥤ Type w) ⟶ G.presheaf)⟩
  mul := ⟨({
      app := fun U => ↾fun p : G.presheaf.obj U × G.presheaf.obj U => p.1 * p.2
      naturality := fun _ _ f => by ext p; exact (G.map_mul f p.1 p.2).symm } :
    G.presheaf ⊗ G.presheaf ⟶ G.presheaf)⟩
  inv := ⟨({
      app := fun U => ↾fun g : G.presheaf.obj U => g⁻¹
      naturality := fun _ _ f => by ext g; exact (_root_.map_inv (G.presheafMapHom f) g).symm } :
    G.presheaf ⟶ G.presheaf)⟩
  one_mul := by ext U x; exact _root_.one_mul (x.2 : G.presheaf.obj U)
  mul_one := by ext U x; exact _root_.mul_one (x.1 : G.presheaf.obj U)
  mul_assoc := by
    ext U x; exact _root_.mul_assoc (x.1.1 : G.presheaf.obj U) (x.1.2 : G.presheaf.obj U) x.2
  left_inv := by ext U x; exact _root_.inv_mul_cancel (x : G.presheaf.obj U)
  right_inv := by ext U x; exact _root_.mul_inv_cancel (x : G.presheaf.obj U)

/-- The group structure on the sections of a group object of sheaves of sets. -/
@[instance_reducible]
def grpObjGroup (P : Sheaf J (Type w)) [GrpObj P] (U : Cᵒᵖ) : Group (P.obj.obj U) where
  mul x y := μ[P].hom.app U (x, y)
  one := η[P].hom.app U PUnit.unit
  inv x := ι[P].hom.app U x
  mul_assoc x y z :=
    congrArg (fun φ => φ.hom.app U (show ((P ⊗ P) ⊗ P).obj.obj U from ((x, y), z)))
      (MonObj.mul_assoc P)
  one_mul x :=
    congrArg (fun φ => φ.hom.app U (show (𝟙_ _ ⊗ P).obj.obj U from (PUnit.unit, x)))
      (MonObj.one_mul P)
  mul_one x :=
    congrArg (fun φ => φ.hom.app U (show (P ⊗ 𝟙_ _).obj.obj U from (x, PUnit.unit)))
      (MonObj.mul_one P)
  inv_mul_cancel x := congrArg (fun φ => φ.hom.app U x) (GrpObj.left_inv P)

/-- **A group object of sheaves of sets is a sheaf of groups**, the group laws on sections being
those of the group object evaluated section-wise. -/
abbrev ofGrpObj (P : Sheaf J (Type w)) [GrpObj P] : SheafOfGroups.{w} J where
  presheaf := P.obj
  isSheaf := P.property
  group := grpObjGroup P
  map_mul {U _V} f x y :=
    (NatTrans.naturality_apply μ[P].hom f (show (P ⊗ P).obj.obj U from (x, y))).symm

/-- The product of two sections of `SheafOfGroups.ofGrpObj P` is the multiplication of the group
object. -/
theorem ofGrpObj_mul (P : Sheaf J (Type w)) [GrpObj P] (U : Cᵒᵖ) (x y : P.obj.obj U) :
    letI := grpObjGroup P U
    x * y = μ[P].hom.app U (x, y) :=
  rfl

/-- The unit section of `SheafOfGroups.ofGrpObj P` is the unit of the group object. -/
theorem ofGrpObj_one (P : Sheaf J (Type w)) [GrpObj P] (U : Cᵒᵖ) :
    letI := grpObjGroup P U
    (1 : P.obj.obj U) = η[P].hom.app U PUnit.unit :=
  rfl

end SheafOfGroups

/-! ### Pseudo-torsors as module objects -/

/-- An isomorphism of sheaves of sets is bijective on sections. -/
private theorem bijective_hom_app_of_isIso {P Q : Sheaf J (Type w)} (f : P ⟶ Q) [IsIso f]
    (U : Cᵒᵖ) : Function.Bijective (f.hom.app U) := by
  have : IsIso ((sheafToPresheaf J (Type w)).map f) := inferInstance
  exact (isIso_iff_bijective _).1
    (inferInstanceAs (IsIso (((sheafToPresheaf J (Type w)).map f).app U)))

namespace PseudoTorsor

variable {G : SheafOfGroups.{w} J}

/-- The underlying sheaf of sets of a pseudo-torsor. -/
abbrev sheaf (F : PseudoTorsor.{w} G) : Sheaf J (Type w) :=
  ⟨F.presheaf, F.isSheaf⟩

/-- A pseudo-torsor is a module object over the group object of its sheaf of groups. -/
instance modObjSheaf (F : PseudoTorsor.{w} G) : ModObj G.sheaf F.sheaf where
  smul := ⟨({
      app := fun U => ↾fun p : G.presheaf.obj U × F.presheaf.obj U => F.act U p.1 p.2
      naturality := fun _ _ f => by ext p; exact (F.naturality f p.1 p.2).symm } :
    G.presheaf ⊗ F.presheaf ⟶ F.presheaf)⟩
  one_smul := by ext U x; exact F.one_act _ x.2
  mul_smul := by ext U x; exact F.mul_act _ x.1.1 x.1.2 x.2

/-- The action morphism of the module object of a pseudo-torsor is the section-wise action. -/
theorem smul_sheaf_hom_app (F : PseudoTorsor.{w} G) (U : Cᵒᵖ)
    (p : G.presheaf.obj U × F.presheaf.obj U) :
    γ[G.sheaf, F.sheaf].hom.app U p = F.act U p.1 p.2 :=
  rfl

/-- The shear map of the module object of a pseudo-torsor is an isomorphism of sheaves. -/
instance isIso_leftSMul_sheaf (F : PseudoTorsor.{w} G) :
    IsIso (ModObj.leftSMul G.sheaf F.sheaf) := by
  have : IsIso ((sheafToPresheaf J (Type w)).map (ModObj.leftSMul G.sheaf F.sheaf)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro U
    rw [isIso_iff_bijective]
    have key : ∀ p : G.presheaf.obj U × F.presheaf.obj U,
        ((sheafToPresheaf J (Type w)).map (ModObj.leftSMul G.sheaf F.sheaf)).app U p =
          (F.act U p.1 p.2, p.2) := fun _ => rfl
    refine ⟨fun p q h => ?_, fun q => ?_⟩
    · replace h := (key p).symm.trans (h.trans (key q))
      obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
      rw [← h₂] at h₁
      exact Prod.ext ((F.simplyTransitive U ⟨p.2⟩ p.2 (F.act U p.1 p.2)).unique rfl h₁.symm) h₂
    · obtain ⟨g, hg, -⟩ := F.simplyTransitive U ⟨q.2⟩ q.2 q.1
      exact ⟨(g, q.2), (key _).trans (Prod.ext hg rfl)⟩
  exact isIso_of_reflects_iso _ (sheafToPresheaf J (Type w))

/-- **A module object with invertible shear map is a pseudo-torsor** under the sheaf of groups
of the group object. -/
def ofModObj (P Q : Sheaf J (Type w)) [GrpObj P] [ModObj P Q] [IsIso (ModObj.leftSMul P Q)] :
    PseudoTorsor.{w} (SheafOfGroups.ofGrpObj P) where
  presheaf := Q.obj
  isSheaf := Q.property
  act U g s := γ[P, Q].hom.app U (g, s)
  one_act U s :=
    congrArg (fun φ => φ.hom.app U (show (𝟙_ _ ⊗ Q).obj.obj U from (PUnit.unit, s)))
      (ModObj.one_smul (M := P) Q)
  mul_act U g h s :=
    congrArg (fun φ => φ.hom.app U (show ((P ⊗ P) ⊗ Q).obj.obj U from ((g, h), s)))
      (ModObj.mul_smul (M := P) Q)
  naturality {U V} f g s :=
    (NatTrans.naturality_apply γ[P, Q].hom f (show (P ⊗ Q).obj.obj U from (g, s))).symm
  simplyTransitive U _ s t := by
    have : IsIso ((sheafToPresheaf J (Type w)).map (ModObj.leftSMul P Q)) := inferInstance
    have hb : Function.Bijective ((ModObj.leftSMul P Q).hom.app U) :=
      (isIso_iff_bijective _).1 (inferInstanceAs (IsIso (((sheafToPresheaf J (Type w)).map
        (ModObj.leftSMul P Q)).app U)))
    obtain ⟨⟨g, s'⟩, hg⟩ := hb.2 (t, s)
    obtain rfl : s' = s := congrArg Prod.snd hg
    refine ⟨g, congrArg Prod.fst hg, fun g' hg' => ?_⟩
    have := hb.1 (a₁ := (g', s')) (a₂ := (g, s')) (by
      change (γ[P, Q].hom.app U (g', s'), s') = (γ[P, Q].hom.app U (g, s'), s')
      rw [show γ[P, Q].hom.app U (g', s') = t from hg']
      exact congrArg (fun p => (p.1, s')) hg.symm)
    exact congrArg Prod.fst this

end PseudoTorsor

/-! ### The image of a sheaf of groups and of its torsors under a functor -/

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  (L : Sheaf J (Type w) ⥤ Sheaf K (Type w)) [PreservesFiniteProducts L]

namespace SheafOfGroups

/-- **The image of a sheaf of groups** under a finite-product-preserving functor of sheaves of
sets: the sections of `L G` with the group structure of the group object `L G`. -/
def map (G : SheafOfGroups.{w} J) : SheafOfGroups.{w} K :=
  letI : GrpObj (L.obj G.sheaf) := Functor.grpObjObj
  ofGrpObj (L.obj G.sheaf)

/-- The product of two sections of `G.map L`: the image of the multiplication of `G`, precomposed
with the monoidal comparison. -/
theorem map_presheaf_mul (G : SheafOfGroups.{w} J) (U : Dᵒᵖ) (x y : (G.map L).presheaf.obj U) :
    x * y = (Functor.LaxMonoidal.μ L G.sheaf G.sheaf ≫ L.map μ[G.sheaf]).hom.app U (x, y) :=
  rfl

end SheafOfGroups

namespace PseudoTorsor

variable {G : SheafOfGroups.{w} J}

/-- The image of the module object of a pseudo-torsor: the image of the action, precomposed with
the monoidal comparison. -/
@[instance_reducible]
def mapModObj (F : PseudoTorsor.{w} G) :
    letI : GrpObj (L.obj G.sheaf) := Functor.grpObjObj
    ModObj (L.obj G.sheaf) (L.obj F.sheaf) :=
  letI : GrpObj (L.obj G.sheaf) := Functor.grpObjObj
  Functor.LaxMonoidal.modObj L _ rfl rfl

/-- The shear map of the image of the module object of a pseudo-torsor is an isomorphism. -/
theorem isIso_leftSMul_map (F : PseudoTorsor.{w} G) :
    letI : GrpObj (L.obj G.sheaf) := Functor.grpObjObj
    letI : ModObj (L.obj G.sheaf) (L.obj F.sheaf) := F.mapModObj L
    IsIso (ModObj.leftSMul (L.obj G.sheaf) (L.obj F.sheaf)) := by
  let : GrpObj (L.obj G.sheaf) := Functor.grpObjObj
  let : ModObj (L.obj G.sheaf) (L.obj F.sheaf) := F.mapModObj L
  have key : ModObj.leftSMul (L.obj G.sheaf) (L.obj F.sheaf) =
      (prodComparisonIso L G.sheaf F.sheaf).inv ≫
        L.map (ModObj.leftSMul G.sheaf F.sheaf) ≫ (prodComparisonIso L F.sheaf F.sheaf).hom :=
    Functor.LaxMonoidal.mapModObj_leftSMul L (M := G.sheaf) (X := F.sheaf) _ rfl rfl
  rw [key]
  infer_instance

/-- **The image of a pseudo-torsor** under a finite-product-preserving functor of sheaves of
sets: a pseudo-torsor under the image of the sheaf of groups. -/
def map (F : PseudoTorsor.{w} G) : PseudoTorsor.{w} (G.map L) :=
  letI : GrpObj (L.obj G.sheaf) := Functor.grpObjObj
  letI : ModObj (L.obj G.sheaf) (L.obj F.sheaf) := F.mapModObj L
  haveI := F.isIso_leftSMul_map L
  ofModObj (L.obj G.sheaf) (L.obj F.sheaf)

/-- The action on the image of a pseudo-torsor is the image of the action, precomposed with the
monoidal comparison. -/
theorem map_act (F : PseudoTorsor.{w} G) (U : Dᵒᵖ) (g : (G.map L).presheaf.obj U)
    (s : (F.map L).presheaf.obj U) :
    (F.map L).act U g s =
      (Functor.LaxMonoidal.μ L G.sheaf F.sheaf ≫ L.map γ[G.sheaf, F.sheaf]).hom.app U (g, s) :=
  rfl

/-- **Equivariance as an identity of morphisms of sheaves.** The underlying morphism of sheaves
of a morphism of pseudo-torsors commutes with the action morphisms. -/
theorem Hom.smul_comp {F F' : PseudoTorsor.{w} G} (e : F.Hom F') :
    γ[G.sheaf, F.sheaf] ≫ (⟨e.hom⟩ : F.sheaf ⟶ F'.sheaf) =
      (G.sheaf ◁ (⟨e.hom⟩ : F.sheaf ⟶ F'.sheaf)) ≫ γ[G.sheaf, F'.sheaf] := by
  ext U x
  exact e.map_act U x.1 x.2

/-- A morphism of sheaves between pseudo-torsors which commutes with the action morphisms is a
morphism of pseudo-torsors. -/
def Hom.ofSheafHom {F F' : PseudoTorsor.{w} G} (φ : F.sheaf ⟶ F'.sheaf)
    (hφ : γ[G.sheaf,F.sheaf] ≫ φ = (G.sheaf ◁ φ) ≫ γ[G.sheaf,F'.sheaf]) : F.Hom F' where
  hom := φ.hom
  map_act U g s := congrArg (fun f : G.sheaf ⊗ F.sheaf ⟶ F'.sheaf => f.hom.app U (g, s)) hφ

/-- The image of a morphism of pseudo-torsors. -/
def Hom.map {F F' : PseudoTorsor.{w} G} (e : F.Hom F') : (F.map L).Hom (F'.map L) where
  hom := (L.map (⟨e.hom⟩ : F.sheaf ⟶ F'.sheaf)).hom
  map_act U g s := by
    have h : (Functor.LaxMonoidal.μ L G.sheaf F.sheaf ≫ L.map γ[G.sheaf, F.sheaf]) ≫
        L.map (⟨e.hom⟩ : F.sheaf ⟶ F'.sheaf) =
        (L.obj G.sheaf ◁ L.map (⟨e.hom⟩ : F.sheaf ⟶ F'.sheaf)) ≫
          Functor.LaxMonoidal.μ L G.sheaf F'.sheaf ≫ L.map γ[G.sheaf, F'.sheaf] := by
      rw [Category.assoc, ← L.map_comp, e.smul_comp, L.map_comp,
        Functor.LaxMonoidal.μ_natural_right_assoc]
    exact congrArg (fun f : L.obj G.sheaf ⊗ L.obj F.sheaf ⟶ L.obj F'.sheaf => f.hom.app U (g, s)) h

/-- **Local nonemptiness is local surjectivity.** A pseudo-torsor is a torsor exactly when its
morphism to the final sheaf is locally surjective. -/
theorem isTorsor_iff_isLocallySurjective (F : PseudoTorsor.{w} G) :
    F.IsTorsor ↔ Sheaf.IsLocallySurjective (toUnit F.sheaf) := by
  constructor
  · intro hF
    refine ⟨fun {U} s => ?_⟩
    obtain ⟨S, hS, hs⟩ := hF U
    refine J.superset_covering (fun V f hf => ?_) hS
    obtain ⟨t⟩ := hs hf
    exact ⟨t, rfl⟩
  · intro hF U
    refine ⟨_, Presheaf.imageSieve_mem J (toUnit F.sheaf).hom (U := op U) PUnit.unit,
      fun V f hf => ?_⟩
    obtain ⟨t, -⟩ := hf
    exact ⟨t⟩

/-- **The image of a torsor is a torsor**, for a functor which preserves epimorphisms: the
morphism to the final sheaf is an epimorphism, and so is its image. -/
theorem isTorsor_map [HasSheafify K (Type w)] [L.PreservesEpimorphisms] {F : PseudoTorsor.{w} G}
    (hF : F.IsTorsor) : (F.map L).IsTorsor := by
  rw [isTorsor_iff_isLocallySurjective] at hF ⊢
  rw [Sheaf.isLocallySurjective_iff_epi]
  rw [show toUnit (F.map L).sheaf = L.map (toUnit F.sheaf) ≫ Functor.OplaxMonoidal.η L from
    toUnit_unique _ _]
  have : Sheaf.IsLocallySurjective (toUnit F.sheaf) := hF
  have : Epi (toUnit F.sheaf) := Sheaf.epi_of_isLocallySurjective' _
  exact epi_comp' (Functor.map_epi L _) inferInstance

end PseudoTorsor

namespace SheafOfGroups

variable {G : SheafOfGroups.{w} J}

/-- **The map on first cohomology** induced by a functor of sheaves of sets which preserves finite
products and epimorphisms: the class of a torsor goes to the class of its image. -/
def TorsorClasses.map [HasSheafify K (Type w)] [L.PreservesEpimorphisms] :
    TorsorClasses.{w} G → TorsorClasses.{w} (G.map L) :=
  Quotient.lift (fun F => TorsorClasses.mk (F.1.map L) (PseudoTorsor.isTorsor_map L F.2))
    (fun _ _ ⟨e, _⟩ => TorsorClasses.mk_eq_mk_of_hom _ _ (e.map L))

/-- The map on first cohomology sends the class of a torsor to the class of its image. -/
theorem TorsorClasses.map_mk [HasSheafify K (Type w)] [L.PreservesEpimorphisms]
    (F : PseudoTorsor.{w} G) (hF : F.IsTorsor) :
    TorsorClasses.map L (TorsorClasses.mk F hF) =
      TorsorClasses.mk (F.map L) (PseudoTorsor.isTorsor_map L hF) :=
  rfl

/-- **The map on first cohomology is injective for a fully faithful functor**: an isomorphism of
the images of two torsors is the image of a morphism of sheaves between them, which commutes with
the actions because its image does. -/
theorem TorsorClasses.map_injective [HasSheafify K (Type w)] [L.PreservesEpimorphisms] [L.Full]
    [L.Faithful] : Function.Injective (TorsorClasses.map L (G := G)) := by
  intro c c' h
  obtain ⟨F, hF, rfl⟩ := TorsorClasses.mk_surjective c
  obtain ⟨F', hF', rfl⟩ := TorsorClasses.mk_surjective c'
  rw [TorsorClasses.map_mk, TorsorClasses.map_mk, TorsorClasses.mk_eq_mk_iff] at h
  obtain ⟨e, -⟩ := h
  let e' : L.obj F.sheaf ⟶ L.obj F'.sheaf := ⟨e.hom⟩
  let φ : F.sheaf ⟶ F'.sheaf := L.preimage e'
  have he : (Functor.LaxMonoidal.μ L G.sheaf F.sheaf ≫ L.map γ[G.sheaf, F.sheaf]) ≫ e' =
      (L.obj G.sheaf ◁ e') ≫ Functor.LaxMonoidal.μ L G.sheaf F'.sheaf ≫
        L.map γ[G.sheaf, F'.sheaf] := by
    ext U x
    exact e.map_act U x.1 x.2
  have hφ : γ[G.sheaf, F.sheaf] ≫ φ = (G.sheaf ◁ φ) ≫ γ[G.sheaf, F'.sheaf] := by
    apply L.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ L G.sheaf F.sheaf)).1
    rw [L.map_comp, L.map_comp, Functor.map_preimage, ← Category.assoc, he,
      ← Functor.LaxMonoidal.μ_natural_right_assoc, Functor.map_preimage]
  exact TorsorClasses.mk_eq_mk_of_hom hF hF' (PseudoTorsor.Hom.ofSheafHom φ hφ)

end SheafOfGroups

/-! ### Torsors with sections locally on the image of a continuous functor -/

section Adjunction

variable {G : SheafOfGroups.{w} J} (u : C ⥤ D) [u.IsContinuous J K]
  {L} (adj : L ⊣ u.sheafPushforwardContinuous (Type w) J K)

namespace SheafOfGroups

/-- The unit `G ⟶ u_* L G` of the adjunction on sections. -/
abbrev unitApp (G : SheafOfGroups.{w} J) (U : Cᵒᵖ) :
    G.presheaf.obj U → (G.map L).presheaf.obj (u.op.obj U) :=
  (adj.unit.app G.sheaf).hom.app U

omit [PreservesFiniteProducts L] in
/-- The image under `L(fst)` of the unit at a section of a product is the unit at its first
component. -/
theorem unit_app_tensor_fst (P Q : Sheaf J (Type w)) (U : Cᵒᵖ) (x : P.obj.obj U × Q.obj.obj U) :
    (L.map (fst P Q)).hom.app (u.op.obj U) ((adj.unit.app (P ⊗ Q)).hom.app U x) =
      (adj.unit.app P).hom.app U x.1 :=
  congrArg (fun f : P ⊗ Q ⟶ (u.sheafPushforwardContinuous (Type w) J K).obj (L.obj P) =>
    f.hom.app U x) (adj.unit.naturality (fst P Q)).symm

omit [PreservesFiniteProducts L] in
/-- The image under `L(snd)` of the unit at a section of a product is the unit at its second
component. -/
theorem unit_app_tensor_snd (P Q : Sheaf J (Type w)) (U : Cᵒᵖ) (x : P.obj.obj U × Q.obj.obj U) :
    (L.map (snd P Q)).hom.app (u.op.obj U) ((adj.unit.app (P ⊗ Q)).hom.app U x) =
      (adj.unit.app Q).hom.app U x.2 :=
  congrArg (fun f : P ⊗ Q ⟶ (u.sheafPushforwardContinuous (Type w) J K).obj (L.obj Q) =>
    f.hom.app U x) (adj.unit.naturality (snd P Q)).symm

/-- The monoidal comparison of `L` applied to the units of two sections is the unit of the pair. -/
theorem μ_unit_app (P Q : Sheaf J (Type w)) (U : Cᵒᵖ) (x : P.obj.obj U × Q.obj.obj U) :
    (Functor.LaxMonoidal.μ L P Q).hom.app (u.op.obj U)
        ((adj.unit.app P).hom.app U x.1, (adj.unit.app Q).hom.app U x.2) =
      (adj.unit.app (P ⊗ Q)).hom.app U x := by
  have h' := congrArg (fun f : L.obj P ⊗ L.obj Q ⟶ L.obj P ⊗ L.obj Q =>
    f.hom.app (u.op.obj U) ((adj.unit.app P).hom.app U x.1, (adj.unit.app Q).hom.app U x.2))
    (Functor.Monoidal.μ_δ L P Q)
  apply (bijective_hom_app_of_isIso (Functor.OplaxMonoidal.δ L P Q) (u.op.obj U)).1
  refine h'.trans (Prod.ext ?_ ?_)
  · exact ((unit_app_tensor_fst u adj P Q U x).symm.trans
      (congrArg (fun f : L.obj (P ⊗ Q) ⟶ L.obj P => f.hom.app (u.op.obj U)
        ((adj.unit.app (P ⊗ Q)).hom.app U x)) (Functor.OplaxMonoidal.δ_fst L P Q)).symm)
  · exact ((unit_app_tensor_snd u adj P Q U x).symm.trans
      (congrArg (fun f : L.obj (P ⊗ Q) ⟶ L.obj Q => f.hom.app (u.op.obj U)
        ((adj.unit.app (P ⊗ Q)).hom.app U x)) (Functor.OplaxMonoidal.δ_snd L P Q)).symm)

/-- The unit of the adjunction is multiplicative on sections. -/
theorem unitApp_mul (G : SheafOfGroups.{w} J) (U : Cᵒᵖ) (a b : G.presheaf.obj U) :
    G.unitApp u adj U (a * b) = G.unitApp u adj U a * G.unitApp u adj U b := by
  rw [map_presheaf_mul]
  have h₁ := congrArg (fun f : G.sheaf ⊗ G.sheaf ⟶
      (u.sheafPushforwardContinuous (Type w) J K).obj (L.obj G.sheaf) => f.hom.app U (a, b))
    (adj.unit.naturality μ[G.sheaf])
  refine h₁.trans ?_
  show (L.map μ[G.sheaf]).hom.app (u.op.obj U) ((adj.unit.app (G.sheaf ⊗ G.sheaf)).hom.app U
      (a, b)) =
    (L.map μ[G.sheaf]).hom.app (u.op.obj U) ((Functor.LaxMonoidal.μ L G.sheaf G.sheaf).hom.app
      (u.op.obj U) (G.unitApp u adj U a, G.unitApp u adj U b))
  rw [μ_unit_app u adj G.sheaf G.sheaf U (a, b)]

/-- The unit of the adjunction on sections, as a homomorphism of groups. -/
def unitAppHom (G : SheafOfGroups.{w} J) (U : Cᵒᵖ) :
    G.presheaf.obj U →* (G.map L).presheaf.obj (u.op.obj U) :=
  MonoidHom.mk' (G.unitApp u adj U) (G.unitApp_mul u adj U)

/-- The unit of the adjunction sends the identity section to the identity. -/
theorem unitApp_one (G : SheafOfGroups.{w} J) (U : Cᵒᵖ) : G.unitApp u adj U 1 = 1 :=
  (G.unitAppHom u adj U).map_one

/-- The unit of the adjunction is compatible with restriction of sections. -/
theorem unitApp_naturality (G : SheafOfGroups.{w} J) {U V : Cᵒᵖ} (f : U ⟶ V)
    (g : G.presheaf.obj U) :
    G.unitApp u adj V (G.presheaf.map f g) =
      (G.map L).presheaf.map (u.op.map f) (G.unitApp u adj U g) :=
  NatTrans.naturality_apply (adj.unit.app G.sheaf).hom f g

omit [PreservesFiniteProducts L] in
/-- If the unit of the adjunction is invertible, it is bijective on sections. -/
theorem unitApp_bijective [IsIso adj.unit] (P : Sheaf J (Type w)) (U : Cᵒᵖ) :
    Function.Bijective ((adj.unit.app P).hom.app U) := by
  exact bijective_hom_app_of_isIso (adj.unit.app P) U

end SheafOfGroups

namespace PseudoTorsor

/-- **The restriction of a pseudo-torsor along `u`.** For a pseudo-torsor `T` under `L G`, the
restriction `u_* T` with `G` acting through the unit `G ⟶ u_* L G`; it is a pseudo-`G`-torsor
when the unit is invertible. -/
def pushforward [IsIso adj.unit] (T : PseudoTorsor.{w} (G.map L)) : PseudoTorsor.{w} G where
  presheaf := u.op ⋙ T.presheaf
  isSheaf := ((u.sheafPushforwardContinuous (Type w) J K).obj T.sheaf).property
  act U g s := T.act (u.op.obj U) (G.unitApp u adj U g) s
  one_act U s := by
    change T.act _ (G.unitApp u adj U 1) s = s
    rw [SheafOfGroups.unitApp_one, T.one_act]
  mul_act U g h s := by
    change T.act _ (G.unitApp u adj U (g * h)) s = _
    rw [SheafOfGroups.unitApp_mul, T.mul_act]
  naturality f g s := by
    change T.presheaf.map (u.op.map f) (T.act _ _ s) =
      T.act _ (G.unitApp u adj _ (G.presheaf.map f g)) (T.presheaf.map (u.op.map f) s)
    rw [T.naturality, SheafOfGroups.unitApp_naturality]
  simplyTransitive U hne s t := by
    obtain ⟨h, hh, huniq⟩ := T.simplyTransitive (u.op.obj U) hne s t
    have hbij := SheafOfGroups.unitApp_bijective u adj G.sheaf U
    obtain ⟨g, rfl⟩ := hbij.2 h
    exact ⟨g, hh, fun g' hg' => hbij.1 (huniq _ hg')⟩

/-- The restriction of a pseudo-torsor along `u` is a torsor as soon as the pseudo-torsor has
sections locally on the image of `u`. -/
theorem isTorsor_pushforward [IsIso adj.unit] (T : PseudoTorsor.{w} (G.map L))
    (hT : ∀ U : C, ∃ S ∈ J U, ∀ ⦃V : C⦄ ⦃f : V ⟶ U⦄, S f →
      Nonempty (T.presheaf.obj (op (u.obj V)))) :
    (T.pushforward u adj).IsTorsor :=
  hT

/-- The counit `L u_* T ⟶ T`, as a morphism of sheaves out of the image of the restriction. -/
abbrev counitSheafHom [IsIso adj.unit] (T : PseudoTorsor.{w} (G.map L)) :
    L.obj (T.pushforward u adj).sheaf ⟶ T.sheaf :=
  adj.counit.app T.sheaf

/-- The counit is equivariant, as an identity of morphisms out of `L(G × u_* T)`. -/
theorem map_smul_comp_counit [IsIso adj.unit] (T : PseudoTorsor.{w} (G.map L)) :
    L.map γ[G.sheaf, (T.pushforward u adj).sheaf] ≫ T.counitSheafHom u adj =
      Functor.OplaxMonoidal.δ L G.sheaf (T.pushforward u adj).sheaf ≫
        (L.obj G.sheaf ◁ T.counitSheafHom u adj) ≫ γ[(G.map L).sheaf, T.sheaf] := by
  set P := (T.pushforward u adj).sheaf
  apply (adj.homEquiv _ _).injective
  ext U x
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have h₁ := congrArg (fun φ => φ.hom.app U x) (adj.unit.naturality γ[G.sheaf, P])
  have h₂ := fun y => congrArg (fun φ => φ.hom.app U y) (adj.right_triangle_components T.sheaf)
  have hδ : (Functor.OplaxMonoidal.δ L G.sheaf P).hom.app (u.op.obj U)
      ((adj.unit.app (G.sheaf ⊗ P)).hom.app U x) =
      ((adj.unit.app G.sheaf).hom.app U x.1, (adj.unit.app P).hom.app U x.2) := by
    rw [← SheafOfGroups.μ_unit_app u adj G.sheaf P U x]
    exact congrArg (fun φ => φ.hom.app (u.op.obj U)
      (show (L.obj G.sheaf ⊗ L.obj P).obj.obj (u.op.obj U) from
        ((adj.unit.app G.sheaf).hom.app U x.1, (adj.unit.app P).hom.app U x.2)))
      (Functor.Monoidal.μ_δ L G.sheaf P)
  show (adj.counit.app T.sheaf).hom.app (u.op.obj U)
      ((L.map γ[G.sheaf, P]).hom.app (u.op.obj U) ((adj.unit.app (G.sheaf ⊗ P)).hom.app U x)) =
    γ[(G.map L).sheaf, T.sheaf].hom.app (u.op.obj U)
      ((L.obj G.sheaf ◁ T.counitSheafHom u adj).hom.app (u.op.obj U)
        ((Functor.OplaxMonoidal.δ L G.sheaf P).hom.app (u.op.obj U)
          ((adj.unit.app (G.sheaf ⊗ P)).hom.app U x)))
  rw [hδ]
  show (adj.counit.app T.sheaf).hom.app (u.op.obj U)
      ((L.map γ[G.sheaf, P]).hom.app (u.op.obj U) ((adj.unit.app (G.sheaf ⊗ P)).hom.app U x)) =
    T.act (u.op.obj U) ((adj.unit.app G.sheaf).hom.app U x.1)
      ((adj.counit.app T.sheaf).hom.app (u.op.obj U) ((adj.unit.app P).hom.app U x.2))
  refine (congrArg (fun y => (adj.counit.app T.sheaf).hom.app (u.op.obj U) y) h₁.symm).trans
    ((h₂ _).trans ?_)
  exact congrArg (T.act (u.op.obj U) ((adj.unit.app G.sheaf).hom.app U x.1)) (h₂ x.2).symm

/-- **The counit `L u_* T ⟶ T` is a morphism of pseudo-torsors.** -/
def counitHom [IsIso adj.unit] (T : PseudoTorsor.{w} (G.map L)) :
    ((T.pushforward u adj).map L).Hom T :=
  Hom.ofSheafHom (F := (T.pushforward u adj).map L) (T.counitSheafHom u adj) (by
    ext U x
    have h := congrArg (fun f => Functor.LaxMonoidal.μ L G.sheaf (T.pushforward u adj).sheaf ≫ f)
      (T.map_smul_comp_counit u adj)
    simp only [Functor.Monoidal.μ_δ_assoc] at h
    rw [← Category.assoc] at h
    exact congrArg (fun φ => φ.hom.app U x) h)

end PseudoTorsor

namespace SheafOfGroups

/-- **Bijectivity on first cohomology.** Let `L` be left adjoint to the restriction `u_*` along a
continuous functor `u`, with invertible unit, and suppose that every torsor under `L G` has
sections locally on the image of `u`. Then `L` induces a bijection `H¹(C, G) ≃ H¹(D, L G)`. -/
theorem TorsorClasses.map_bijective_of_adjunction [HasSheafify K (Type w)]
    [L.PreservesEpimorphisms] [IsIso adj.unit]
    (hloc : ∀ T : PseudoTorsor.{w} (G.map L), T.IsTorsor → ∀ U : C, ∃ S ∈ J U,
      ∀ ⦃V : C⦄ ⦃f : V ⟶ U⦄, S f → Nonempty (T.presheaf.obj (op (u.obj V)))) :
    Function.Bijective (TorsorClasses.map L (G := G)) := by
  have hL := adj.fullyFaithfulLOfIsIsoUnit
  have := hL.full
  have := hL.faithful
  refine ⟨TorsorClasses.map_injective L, fun c => ?_⟩
  obtain ⟨T, hT, rfl⟩ := TorsorClasses.mk_surjective c
  exact ⟨TorsorClasses.mk _ (PseudoTorsor.isTorsor_pushforward u adj T (hloc T hT)),
    TorsorClasses.mk_eq_mk_of_hom _ hT (PseudoTorsor.counitHom u adj T)⟩

end SheafOfGroups

end Adjunction
