module

public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Space

/-!
# The points of a presheaf on the big fppf site over the spectra of small algebras

Let `T'` be an object of the big fppf site over `S` with affine underlying scheme, and write
`A' = Γ(T', ⊤)`. Every `A'`-algebra `C` below the cutoff of the site gives the object
`Spec C → Spec A' ≅ T' → S` of the site (`specOver`), contravariantly in `C`. A presheaf `X` on
the site therefore restricts to a functor on the small `A'`-algebras (`pointsFunctor`), and a
section of `X` over `Spec P` is a chart of it by `P` (`chartOfPoint`).

## Main definitions

* `AlgebraicGeometry.Stack.GroupoidLift.specOver`, `specOverMap`.
* `AlgebraicGeometry.Stack.GroupoidLift.pointsFunctor`.
* `AlgebraicGeometry.Stack.GroupoidLift.chartOfPoint`.
* `AlgebraicGeometry.Stack.GroupoidLift.relPoints`, `relChart`: the same over `T'` for a
  presheaf `X` with a map `π : X ⟶ yoneda.obj T'`.

## Main results

* `AlgebraicGeometry.Stack.GroupoidLift.exists_specOverMap`, `specOverMap_injective`: the
  morphisms `Spec D ⟶ Spec C` over `T'` are the `Γ(T')`-algebra maps `C → D`.
* `AlgebraicGeometry.Stack.GroupoidLift.relChart_isFormallyEtale`: the chart of a point whose
  Yoneda map is formally étale is formally étale.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T' : BigFppfOver B S hS)

/-- The ring of global sections of the underlying scheme of `T'`. -/
abbrev ringOf : Type u := Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)

variable {B S hS T'}

/-- `Spec C` of a small `Γ(T')`-algebra `C` is contained in the site. -/
theorem contains_spec (C : SmallAlg (ringOf B S hS T') B.cutoff) :
    B.Contains (Spec (CommRingCat.of C.obj)) := by
  show (Spec (CommRingCat.of C.obj)).size < B.cutoff
  rw [Scheme.size_Spec]
  exact max_lt B.aleph0_lt_cutoff C.property

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

/-- The structure morphism `Spec C → Spec A' ≅ T'`. -/
noncomputable def specToBase (C : SmallAlg (ringOf B S hS T') B.cutoff) :
    Spec (CommRingCat.of C.obj) ⟶ (BigFppfOver.toScheme B S hS).obj T' :=
  Spec.map (CommRingCat.ofHom (algebraMap (ringOf B S hS T') C.obj)) ≫
    ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv

/-- `Spec C` as an object of the big fppf site over `S`, through `T'`. -/
noncomputable def specOver (C : SmallAlg (ringOf B S hS T') B.cutoff) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_spec C) (specToBase C ≫ B.inclusion.map T'.hom)

/-- `specToBase` is compatible with the morphism `Spec D → Spec C` induced by `C → D`. -/
theorem specMap_comp_specToBase {C D : SmallAlg (ringOf B S hS T') B.cutoff} (f : C ⟶ D) :
    Spec.map (CommRingCat.ofHom (f.hom.hom : C.obj →+* D.obj)) ≫ specToBase C = specToBase D := by
  rw [specToBase, specToBase, ← Category.assoc, ← Spec.map_comp]
  congr 2
  ext x
  exact f.hom.hom.commutes x

/-- The morphism `Spec D → Spec C` of the site induced by `C → D`. -/
noncomputable def specOverMap {C D : SmallAlg (ringOf B S hS T') B.cutoff} (f : C ⟶ D) :
    specOver D ⟶ specOver C :=
  BigFppfOver.homMk B S hS (contains_spec C) (specToBase C ≫ B.inclusion.map T'.hom)
    (T := specOver D)
    (show (BigFppfOver.toScheme B S hS).obj (specOver D) ⟶ Spec (CommRingCat.of C.obj) from
      Spec.map (CommRingCat.ofHom (f.hom.hom : C.obj →+* D.obj)))
    (by
      change Spec.map (CommRingCat.ofHom (f.hom.hom : C.obj →+* D.obj)) ≫
        specToBase C ≫ B.inclusion.map T'.hom = specToBase D ≫ B.inclusion.map T'.hom
      rw [← Category.assoc, specMap_comp_specToBase])

/-- The underlying morphism of schemes of `specOverMap f` is `Spec.map f`. -/
theorem toScheme_map_specOverMap {C D : SmallAlg (ringOf B S hS T') B.cutoff} (f : C ⟶ D) :
    (BigFppfOver.toScheme B S hS).map (specOverMap f) =
      Spec.map (CommRingCat.ofHom (f.hom.hom : C.obj →+* D.obj)) :=
  rfl

/-- `specOverMap` takes the identity to the identity. -/
theorem specOverMap_id (C : SmallAlg (ringOf B S hS T') B.cutoff) :
    specOverMap (𝟙 C) = 𝟙 _ := by
  apply BigFppfOver.map_toScheme_injective B S hS
  dsimp only
  rw [CategoryTheory.Functor.map_id]
  exact Spec.map_id (CommRingCat.of C.obj)

/-- `specOverMap` takes a composite to the composite in the opposite order. -/
theorem specOverMap_comp {C D E : SmallAlg (ringOf B S hS T') B.cutoff} (f : C ⟶ D)
    (g : D ⟶ E) : specOverMap (f ≫ g) = specOverMap g ≫ specOverMap f := by
  apply BigFppfOver.map_toScheme_injective B S hS
  dsimp only
  rw [Functor.map_comp]
  exact Spec.map_comp (CommRingCat.ofHom (f.hom.hom : C.obj →+* D.obj))
    (CommRingCat.ofHom (g.hom.hom : D.obj →+* E.obj))

variable (T') in
/-- The points of a presheaf over the spectra of the small `Γ(T')`-algebras. -/
noncomputable def pointsFunctor (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    SmallAlg (ringOf B S hS T') B.cutoff ⥤ Type u where
  obj C := X.obj (op (specOver C))
  map f := X.map (specOverMap f).op
  map_id C := by rw [specOverMap_id, op_id, X.map_id]
  map_comp f g := by rw [specOverMap_comp, op_comp, X.map_comp]

/-- A section of a presheaf over `Spec P` is a chart of its points by `P`. -/
noncomputable def chartOfPoint {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (P : SmallAlg (ringOf B S hS T') B.cutoff) (p : X.obj (op (specOver P))) :
    Chart (pointsFunctor T' X) P.obj where
  app C ℓ := X.map (specOverMap (SmallAlg.homMk ℓ)).op p
  natural f ℓ := by
    change X.map (specOverMap f).op (X.map (specOverMap (SmallAlg.homMk ℓ)).op p) = _
    rw [← Functor.map_comp_apply, ← op_comp, ← specOverMap_comp]
    rfl

/-- The structure morphism `Spec C → T'` in the site. -/
noncomputable def specOverToBase (C : SmallAlg (ringOf B S hS T') B.cutoff) :
    specOver C ⟶ T' :=
  Over.homMk (ObjectProperty.homMk (specToBase C)) rfl

/-- `specOverMap f` lies over `T'`. -/
theorem specOverMap_comp_toBase {C D : SmallAlg (ringOf B S hS T') B.cutoff} (f : C ⟶ D) :
    specOverMap f ≫ specOverToBase C = specOverToBase D := by
  apply BigFppfOver.map_toScheme_injective B S hS
  exact specMap_comp_specToBase f

variable (T') in
/-- The points over `T'` of a presheaf over `T'`. -/
noncomputable def relPoints {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (π : X ⟶ yoneda.obj T') : SmallAlg (ringOf B S hS T') B.cutoff ⥤ Type u where
  obj C := {ξ : X.obj (op (specOver C)) // π.app _ ξ = specOverToBase C}
  map f := TypeCat.ofHom fun ξ ↦ ⟨X.map (specOverMap f).op ξ.1, by
    rw [NatTrans.naturality_apply, ξ.2]
    exact specOverMap_comp_toBase f⟩
  map_id C := ConcreteCategory.hom_ext _ _ fun ξ ↦ Subtype.ext (by
    change X.map (specOverMap (𝟙 C)).op ξ.1 = ξ.1
    rw [specOverMap_id, op_id, Functor.map_id_apply])
  map_comp f g := ConcreteCategory.hom_ext _ _ fun ξ ↦ Subtype.ext (by
    change X.map (specOverMap (f ≫ g)).op ξ.1 =
      X.map (specOverMap g).op (X.map (specOverMap f).op ξ.1)
    rw [specOverMap_comp, op_comp, Functor.map_comp_apply])

/-- The underlying section of `(relPoints T' π).map f ξ` is the restriction of that of `ξ`. -/
theorem relPoints_map_val {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : X ⟶ yoneda.obj T')
    {C D : SmallAlg (ringOf B S hS T') B.cutoff} (f : C ⟶ D) (ξ : (relPoints T' π).obj C) :
    ((relPoints T' π).map f ξ).1 = X.map (specOverMap f).op ξ.1 := rfl

/-- A point over `T'` of a presheaf over `T'`, over `Spec P`, is a chart of its points over `T'`
by `P`. -/
noncomputable def relChart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : X ⟶ yoneda.obj T')
    (P : SmallAlg (ringOf B S hS T') B.cutoff) (p : (relPoints T' π).obj P) :
    Chart (relPoints T' π) P.obj where
  app C ℓ := (relPoints T' π).map (SmallAlg.homMk ℓ) p
  natural f ℓ := by
    rw [← Functor.map_comp_apply]
    rfl

/-- Morphisms of small `A'`-algebras are equal if their underlying ring maps are. -/
private theorem smallAlg_hom_ext {A' : Type u} [CommRing A'] {κ : Cardinal.{u}}
    {C D : SmallAlg A' κ} {f g : C ⟶ D} (h : f.hom.hom = g.hom.hom) : f = g :=
  ObjectProperty.hom_ext _ (CommAlgCat.hom_ext h)

/-- `specOverMap` is injective. -/
theorem specOverMap_injective {C D : SmallAlg (ringOf B S hS T') B.cutoff} {f g : C ⟶ D}
    (h : specOverMap f = specOverMap g) : f = g := by
  have h' := congrArg (fun k ↦ (BigFppfOver.toScheme B S hS).map k) h
  simp only [toScheme_map_specOverMap] at h'
  apply smallAlg_hom_ext
  ext x
  exact congrArg (fun φ : CommRingCat.of C.obj ⟶ CommRingCat.of D.obj ↦ φ.hom x)
    (Spec.map_injective h')

/-- `specOverMap` turns a factorisation `f ≫ g = h` into the reversed factorisation, and
conversely. -/
private theorem comp_eq_iff_specOverMap_comp_eq {C D E : SmallAlg (ringOf B S hS T') B.cutoff}
    {f : C ⟶ D} {g : D ⟶ E} {h : C ⟶ E} :
    f ≫ g = h ↔ specOverMap g ≫ specOverMap f = specOverMap h := by
  rw [← specOverMap_comp]
  exact ⟨congrArg _, specOverMap_injective⟩

/-- Every morphism of the site from `Spec D` to `Spec C` over `T'` comes from an
`A'`-algebra map. -/
theorem exists_specOverMap {C D : SmallAlg (ringOf B S hS T') B.cutoff}
    (g : specOver D ⟶ specOver C) (hg : g ≫ specOverToBase C = specOverToBase D) :
    ∃ f : C ⟶ D, specOverMap f = g := by
  obtain ⟨φ, hφ⟩ : ∃ φ : CommRingCat.of C.obj ⟶ CommRingCat.of D.obj,
      Spec.map φ = (BigFppfOver.toScheme B S hS).map g :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  have hcomp : Spec.map φ ≫ specToBase C = specToBase D := by
    rw [hφ]
    exact congrArg (fun k ↦ (BigFppfOver.toScheme B S hS).map k) hg
  have halg : CommRingCat.ofHom (algebraMap (ringOf B S hS T') C.obj) ≫ φ =
      CommRingCat.ofHom (algebraMap (ringOf B S hS T') D.obj) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    simp only [specToBase, ← Category.assoc] at hcomp
    exact (cancel_mono _).mp hcomp
  let f : C.obj →ₐ[ringOf B S hS T'] D.obj :=
    { φ.hom with commutes' := fun r ↦ congrArg (fun k ↦ k.hom r) halg }
  exact ⟨SmallAlg.homMk f, BigFppfOver.map_toScheme_injective B S hS hφ⟩

/-- The morphism `Spec Q ⟶ Spec R` of the site induced by a surjection `R → Q` with square-zero
kernel is a square-zero closed immersion. -/
theorem isSquareZeroClosedImmersion_specOverMap {R Q : SmallAlg (ringOf B S hS T') B.cutoff}
    (q : R ⟶ Q) (hq : Function.Surjective q.hom.hom)
    (hsq : (RingHom.ker (q.hom.hom : R.obj →+* Q.obj)) ^ 2 = ⊥) :
    Space.IsSquareZeroClosedImmersion B S hS (specOverMap q) :=
  Space.isSquareZeroClosedImmersion_of_specMap B S hS
    (CommRingCat.ofHom (q.hom.hom : R.obj →+* Q.obj)) hq hsq (specOver Q) (specOver R)
    (specOverMap q) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The underlying scheme of `specOver C` is affine. -/
instance (C : SmallAlg (ringOf B S hS T') B.cutoff) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (specOver C)) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of C.obj)))

/-- The chart of a point over `T'` whose Yoneda map is formally étale is formally étale. -/
theorem relChart_isFormallyEtale {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (π : X ⟶ yoneda.obj T') (P : SmallAlg (ringOf B S hS T') B.cutoff)
    (p : (relPoints T' π).obj P) (hp : Space.FormallyEtale (yonedaEquiv.symm p.1)) :
    (relChart π P p).IsFormallyEtale := by
  intro R Q q hq hsq c z hz
  have hcompat : (yonedaEquiv.symm p.1).app (op (specOver Q)) (specOverMap (SmallAlg.homMk c)) =
      X.map (specOverMap q).op z.1 := by
    rw [yonedaEquiv_symm_app_apply]
    exact (congrArg Subtype.val hz).symm
  obtain ⟨g, ⟨hg₁, hg₂⟩, huniq⟩ := hp (specOver Q) (specOver R) inferInstance inferInstance
    (specOverMap q) (isSquareZeroClosedImmersion_specOverMap q hq hsq) _ z.1 hcompat
  have hg₂' : X.map g.op p.1 = z.1 := hg₂
  have hg₁' : specOverMap q ≫ g = specOverMap (SmallAlg.homMk c) := hg₁
  have hp2 : π.app _ p.1 = specOverToBase P := p.2
  have hz2 : π.app _ z.1 = specOverToBase R := z.2
  have hbase : g ≫ specOverToBase P = specOverToBase R := by
    have h := NatTrans.naturality_apply π g.op p.1
    rw [hg₂', hz2, hp2] at h
    exact h.symm
  obtain ⟨f, hf⟩ := exists_specOverMap g hbase
  have hfq : f ≫ q = SmallAlg.homMk c := by
    rw [comp_eq_iff_specOverMap_comp_eq, hf]
    exact hg₁'
  refine ⟨f.hom.hom, ⟨congrArg (fun k ↦ k.hom.hom) hfq, Subtype.ext ?_⟩, ?_⟩
  · show X.map (specOverMap (SmallAlg.homMk f.hom.hom)).op p.1 = z.1
    rw [show SmallAlg.homMk f.hom.hom = f from rfl, hf, hg₂']
  · rintro ℓ ⟨hℓ₁, hℓ₂⟩
    have hgℓ : specOverMap (SmallAlg.homMk ℓ) = g := by
      refine huniq _ ⟨?_, ?_⟩
      · exact comp_eq_iff_specOverMap_comp_eq.1 (smallAlg_hom_ext hℓ₁)
      · exact congrArg Subtype.val hℓ₂
    exact congrArg (fun k ↦ k.hom.hom) (specOverMap_injective (hgℓ.trans hf.symm))

end AlgebraicGeometry.Stack.GroupoidLift

end
