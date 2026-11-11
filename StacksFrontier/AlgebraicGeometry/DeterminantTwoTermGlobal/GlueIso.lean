module

public import StacksFrontier.AlgebraicGeometry.DeterminantTwoTermGlobal.Glue
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.AffineOpenSections

/-!
# Recognising the glued sheaf of a compatible system of modules

Let `D` be a compatible system of finite projective modules on the affine opens of a scheme `X`
(`AlgebraicGeometry.AffineLineSystem`), glued to the sheaf of `𝒪_X`-modules `D.toModules`. A
quasi-coherent `𝒪_X`-module `G` whose sections over every affine open `V` are identified with
`D(V)`, compatibly with restriction, is isomorphic to `D.toModules`: the identifications assemble
to a morphism `G ⟶ D.toModules` sending a section `b` over `U` to the compatible family of the
images of its restrictions to the affine opens `V ⊆ U`, and this morphism is bijective on sections
over affine opens.

## Main definitions

* `AlgebraicGeometry.AffineLineSystem.homOfSectionsEquiv`: the morphism `G ⟶ D.toModules`.
* `AlgebraicGeometry.AffineLineSystem.isoOfSectionsEquiv`: the isomorphism `D.toModules ≅ G`.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.AffineLineSystem

variable {X : Scheme.{u}} (D : AffineLineSystem X) (G : X.Modules)
  (e : ∀ V : X.affineOpens, D.obj V ≃ₗ[Γ(X, V)] Γ(G, V))
  (he : ∀ {V W : X.affineOpens} (h : (W : X.Opens) ≤ V) (x : D.obj V),
    e W (D.map h x) = G.presheaf.map (homOfLE h).op (e V x))

attribute [local instance] moduleBelow

/-- Restricting a section of `G` along `f₁` and then `f₂` is restricting it along `f₂ ≫ f₁`. -/
theorem map_comp_modules {U₁ U₂ U₃ : X.Opens} (f₁ : U₂ ⟶ U₁) (f₂ : U₃ ⟶ U₂) (x : Γ(G, U₁)) :
    G.presheaf.map f₂.op (G.presheaf.map f₁.op x) = G.presheaf.map (f₂ ≫ f₁).op x := by
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

/-- Restricting a section of `G` along an endomorphism of `U` is the identity. -/
theorem map_modules_id {U : X.Opens} (f : U ⟶ U) (x : Γ(G, U)) : G.presheaf.map f.op x = x := by
  rw [Subsingleton.elim f (𝟙 U), op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- The compatible family of the images under `e` of the restrictions of a section of `G` over
`U` to the affine opens contained in `U`. -/
def familyOfSectionsEquiv (U : X.Opens) (b : Γ(G, U)) : D.Sections U :=
  ⟨fun V => (e V.1).symm (G.presheaf.map (homOfLE V.2).op b), fun V W h => by
    apply (e W.1).injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_comp_modules]
    rfl⟩

/-- The value of `familyOfSectionsEquiv` at an affine open `V ⊆ U`. -/
theorem familyOfSectionsEquiv_apply (U : X.Opens) (b : Γ(G, U)) (V : AffBelow U) :
    (D.familyOfSectionsEquiv G e he U b).1 V =
      (e V.1).symm (G.presheaf.map (homOfLE V.2).op b) := rfl

/-- `familyOfSectionsEquiv` as a `Γ(X, U)`-linear map. -/
def familyOfSectionsEquivₗ (U : X.Opens) : Γ(G, U) →ₗ[Γ(X, U)] D.Sections U where
  toFun := D.familyOfSectionsEquiv G e he U
  map_add' a b := Subtype.ext (funext fun V => by
    change (e V.1).symm (G.presheaf.map (homOfLE V.2).op (a + b)) =
      (e V.1).symm (G.presheaf.map (homOfLE V.2).op a) +
        (e V.1).symm (G.presheaf.map (homOfLE V.2).op b)
    rw [map_add, map_add])
  map_smul' r b := Subtype.ext (funext fun V => by
    change (e V.1).symm (G.presheaf.map (homOfLE V.2).op (r • b)) =
      X.presheaf.map (homOfLE V.2).op r • (e V.1).symm (G.presheaf.map (homOfLE V.2).op b)
    rw [Scheme.Modules.map_smul, map_smul])

/-- `familyOfSectionsEquiv` commutes with restriction. -/
theorem familyOfSectionsEquiv_restrict {U U' : X.Opens} (h : U' ≤ U) (b : Γ(G, U)) :
    D.familyOfSectionsEquiv G e he U' (G.presheaf.map (homOfLE h).op b) =
      D.restrict h (D.familyOfSectionsEquiv G e he U b) := by
  refine Subtype.ext (funext fun V => ?_)
  change (e V.1).symm (G.presheaf.map (homOfLE V.2).op (G.presheaf.map (homOfLE h).op b)) =
    (e V.1).symm (G.presheaf.map (homOfLE (V.2.trans h)).op b)
  rw [map_comp_modules]
  rfl

variable [∀ V : X.affineOpens, Module.Finite Γ(X, V) (D.obj V)]
  [∀ V : X.affineOpens, Module.Projective Γ(X, V) (D.obj V)]

/-- The families `familyOfSectionsEquiv`, as a map of presheaves of abelian groups. -/
def homPresheafOfSectionsEquiv : G.presheaf ⟶ D.toModules.presheaf where
  app U := AddCommGrpCat.ofHom (D.familyOfSectionsEquivₗ G e he U.unop).toAddMonoidHom
  naturality {U U'} i := by
    ext b
    exact D.familyOfSectionsEquiv_restrict G e he i.unop.le b

/-- **The morphism `G ⟶ D.toModules`** sending a section of `G` over `U` to the compatible family
of the images under `e` of its restrictions to the affine opens contained in `U`. -/
def homOfSectionsEquiv : G ⟶ D.toModules :=
  ⟨PresheafOfModules.homMk (D.homPresheafOfSectionsEquiv G e he) fun U r b =>
    (D.familyOfSectionsEquivₗ G e he U.unop).map_smul r b⟩

/-- On sections over `U`, `homOfSectionsEquiv` is `familyOfSectionsEquiv`. -/
theorem sec_homOfSectionsEquiv_app (U : X.Opens) (b : Γ(G, U)) :
    D.sec U ((D.homOfSectionsEquiv G e he).app U b) = D.familyOfSectionsEquiv G e he U b := rfl

/-- Over an affine open `V`, `homOfSectionsEquiv` is the inverse of `e V` followed by the
identification of the sections of the glued sheaf with `D(V)`. -/
theorem homOfSectionsEquiv_app_affine (V : X.affineOpens) (b : Γ(G, V)) :
    (D.homOfSectionsEquiv G e he).app V b = (D.sectionsEquiv V).symm ((e V).symm b) := by
  rw [LinearEquiv.eq_symm_apply, sectionsEquiv_apply, sec_homOfSectionsEquiv_app,
    familyOfSectionsEquiv_apply, map_modules_id]

/-- `homOfSectionsEquiv` is bijective on sections over affine opens. -/
theorem bijective_homOfSectionsEquiv_app (V : X.affineOpens) :
    Function.Bijective ((D.homOfSectionsEquiv G e he).val.app (op (V : X.Opens))) := by
  have : ⇑((D.homOfSectionsEquiv G e he).val.app (op (V : X.Opens))) =
      (D.sectionsEquiv V).symm ∘ (e V).symm :=
    funext (D.homOfSectionsEquiv_app_affine G e he V)
  rw [this]
  exact (D.sectionsEquiv V).symm.bijective.comp (e V).symm.bijective

variable [G.IsQuasicoherent]

/-- `homOfSectionsEquiv` is an isomorphism. -/
instance isIso_homOfSectionsEquiv : IsIso (D.homOfSectionsEquiv G e he) := by
  have := D.isQuasicoherent_toModules
  exact Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover _
    (fun V : X.affineOpens => (V : X.Opens)) (iSup_affineOpens_eq_top X) (fun V => V.2)
    (D.bijective_homOfSectionsEquiv_app G e he)

/-- **Recognition of the glued sheaf.** A quasi-coherent `𝒪_X`-module `G` whose sections over
the affine opens are identified with the system `D`, compatibly with restriction, is isomorphic to
the glued sheaf `D.toModules`. -/
def isoOfSectionsEquiv : D.toModules ≅ G :=
  (asIso (D.homOfSectionsEquiv G e he)).symm

/-- Over an affine open `V`, the isomorphism `isoOfSectionsEquiv` is `e V` after the
identification of the sections of the glued sheaf with `D(V)`. -/
theorem isoOfSectionsEquiv_hom_app (V : X.affineOpens) (a : Γ(D.toModules, V)) :
    (D.isoOfSectionsEquiv G e he).hom.val.app (op (V : X.Opens)) a =
      e V (D.sectionsEquiv V a) := by
  have hc : (D.homOfSectionsEquiv G e he).app V
      ((D.isoOfSectionsEquiv G e he).hom.app V a) = a := by
    change ((D.isoOfSectionsEquiv G e he).hom ≫ (D.isoOfSectionsEquiv G e he).inv).app V a = a
    rw [Iso.hom_inv_id]
    rfl
  rw [homOfSectionsEquiv_app_affine, LinearEquiv.symm_apply_eq, LinearEquiv.symm_apply_eq] at hc
  exact hc

/-- Over an affine open `V`, the inverse of `isoOfSectionsEquiv` is the inverse of `e V` after the
identification of the sections of the glued sheaf with `D(V)`. -/
theorem isoOfSectionsEquiv_inv_app (V : X.affineOpens) (b : Γ(G, V)) :
    D.sectionsEquiv V ((D.isoOfSectionsEquiv G e he).inv.val.app (op (V : X.Opens)) b) =
      (e V).symm b := by
  change D.sectionsEquiv V ((D.homOfSectionsEquiv G e he).app V b) = _
  rw [homOfSectionsEquiv_app_affine, LinearEquiv.apply_symm_apply]

/-- Over an arbitrary open `U`, the inverse of `isoOfSectionsEquiv` sends a section `b` of `G`
to the compatible family of the images under `e` of its restrictions to the affine opens
`V ⊆ U`. -/
theorem sec_isoOfSectionsEquiv_inv_app (U : X.Opens) (b : Γ(G, U)) (V : AffBelow U) :
    (D.sec U ((D.isoOfSectionsEquiv G e he).inv.val.app (op U) b)).1 V =
      (e V.1).symm (G.presheaf.map (homOfLE V.2).op b) := rfl

end AlgebraicGeometry.AffineLineSystem

end
