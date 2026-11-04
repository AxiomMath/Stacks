module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapFlat
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.MapHomologicalComplexHomologyIsoNatTrans
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.DerivedPushoutGlueingRestriction
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapMate
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompCancel

/-!
# Naturality of the base-change map on cohomology in the square

Given a morphism from a commutative square of rings `R → A`, `R → R'`, `A → A'`, `R' → A'` to a
second one `R₁ → A₁`, `R₁ → R₁'`, `A₁ → A₁'`, `R₁' → A₁'`, the base-change maps of Stacks 0DJ7
of the two squares, at `K` and at `K ⊗ᴸ_A A₁`, are compatible with the maps induced on
cohomology by derived base change.

## Main results

* `RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq_hom_app`: the composition
  isomorphism along an equation `h ∘ f = c` is the composition isomorphism followed by the
  transport along the equation.
* `RingTheory.TorIndependence.compOfEq_cube`: the composition isomorphisms of derived extension
  of scalars around a morphism of commutative squares of rings are coherent.

## References

* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

/-! ### Composition isomorphisms along equations -/

section CompOfEq

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]

/-- Degreewise, the two composition isomorphisms of extension of scalars agree. -/
theorem modelComp_extendScalarsComp_eq (f : R →+* A) (g : A →+* B) :
    StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u} f g =
      ModuleCat.extendScalarsComp f g := by
  refine Iso.ext (NatTrans.ext (funext fun M => ?_))
  refine ModuleCat.ExtendScalars.hom_ext fun m => ?_
  refine (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp_hom_app_one_tmul.{u, u, u, u}
    f g M m).trans ?_
  exact (ModuleCat.extendScalarsComp_hom_app_one_tmul f g M m).symm

/-- The composition isomorphism `D_f ⋙ D_g ≅ D_{g ∘ f}` along the defining equation is
`totalDerivedExtensionScalarsComp`. -/
theorem totalDerivedExtensionScalarsCompOfEq_rfl (f : R →+* A) (g : A →+* B) :
    totalDerivedExtensionScalarsCompOfEq f g (g.comp f) rfl =
      CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u} f g := by
  let Tf := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f
  let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g
  let Tc := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (g.comp f)
  haveI := Tc.isLeftDerived
  refine Iso.ext (Functor.leftDerived_ext Tc.functor Tc.comparison
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) _ _ _ ?_)
  ext P
  change (totalDerivedExtensionScalarsCompOfEq f g (g.comp f) rfl).hom.app
      (DerivedCategory.Q.obj P) ≫ Tc.comparison.app P =
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
      f g).hom.app (DerivedCategory.Q.obj P) ≫ Tc.comparison.app P
  rw [StacksDraft.DerivedExtensionScalarsModelComp.compModelIso_hom_app_comp_comparison,
    ← CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_comparison]
  simp only [StacksDraft.DerivedExtensionScalarsModelComp.compComparisonOfEq,
    StacksDraft.DerivedExtensionScalarsModelComp.compComparison, eqToHom_refl,
    Category.comp_id, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  refine congrArg (fun t => Tg.functor.map (Tf.comparison.app P) ≫
    Tg.comparison.app _ ≫ t) ?_
  simp only [StacksDraft.DerivedExtensionScalarsModelComp.extensionOfScalarsComplexCompIso,
    CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexComp,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    modelComp_extendScalarsComp_eq]
  rfl

/-- **The composition isomorphism along an equation** is the composition isomorphism followed by
the transport along the equation. -/
theorem totalDerivedExtensionScalarsCompOfEq_hom_app (f : R →+* A) (g : A →+* B) (c : R →+* B)
    (hc : g.comp f = c) (X : DerivedCategory (ModuleCat.{u} R)) :
    (totalDerivedExtensionScalarsCompOfEq f g c hc).hom.app X =
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
          f g).hom.app X ≫
        eqToHom (congrArg (fun φ : R →+* B =>
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            φ).functor.obj X) hc) := by
  subst hc
  rw [totalDerivedExtensionScalarsCompOfEq_rfl, eqToHom_refl, Category.comp_id]

/-- Transport along an equation in the second slot of the composition isomorphism. -/
theorem eqToHom_comp_totalDerivedExtensionScalarsComp (f : R →+* A) {p p' : A →+* B}
    (hp : p = p') (X : DerivedCategory (ModuleCat.{u} R)) :
    eqToHom (congrArg (fun φ : A →+* B =>
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          φ).functor.obj
          ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            f).functor.obj X)) hp) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        f p').hom.app X =
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        f p).hom.app X ≫
      eqToHom (congrArg (fun φ : A →+* B =>
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (φ.comp f)).functor.obj X) hp) := by
  subst hp
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Transport along an equation in the first slot of the composition isomorphism. -/
theorem map_eqToHom_comp_totalDerivedExtensionScalarsComp {p p' : R →+* A} (hp : p = p')
    (g : A →+* B) (X : DerivedCategory (ModuleCat.{u} R)) :
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        g).functor.map (eqToHom (congrArg (fun φ : R →+* A =>
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            φ).functor.obj X) hp)) ≫
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        p' g).hom.app X =
    (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
        p g).hom.app X ≫
      eqToHom (congrArg (fun φ : R →+* A =>
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          (g.comp φ)).functor.obj X) hp) := by
  subst hp
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

/-- The inverse of the composition isomorphism along an equation. -/
theorem totalDerivedExtensionScalarsCompOfEq_inv_app (f : R →+* A) (g : A →+* B) (c : R →+* B)
    (hc : g.comp f = c) (X : DerivedCategory (ModuleCat.{u} R)) :
    (totalDerivedExtensionScalarsCompOfEq f g c hc).inv.app X =
      eqToHom (congrArg (fun φ : R →+* B =>
          (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
            φ).functor.obj X) hc.symm) ≫
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u}
          f g).inv.app X := by
  subst hc
  rw [totalDerivedExtensionScalarsCompOfEq_rfl, eqToHom_refl, Category.id_comp]

end CompOfEq

/-! ### Normal forms of triple composites -/

section Steps

variable {X Y Y' Z Z' W : Type u} [CommRing X] [CommRing Y] [CommRing Y'] [CommRing Z]
  [CommRing Z'] [CommRing W]

/-- The derived extension of scalars along `φ`. -/
abbrev dext {S T : Type u} [CommRing S] [CommRing T] (φ : S →+* T) :
    DerivedCategory (ModuleCat.{u} S) ⥤ DerivedCategory (ModuleCat.{u} T) :=
  (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} φ).functor

/-- The composition isomorphism `D_φ ⋙ D_ψ ≅ D_{ψ ∘ φ}`. -/
abbrev dcomp {S T V : Type u} [CommRing S] [CommRing T] [CommRing V] (φ : S →+* T)
    (ψ : T →+* V) : dext φ ⋙ dext ψ ≅ dext (ψ.comp φ) :=
  CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp.{u, u} φ ψ

/-- The transport `D_φ N ⟶ D_ψ N` along an equation `φ = ψ`. -/
abbrev dtr {S T : Type u} [CommRing S] [CommRing T] {φ ψ : S →+* T} (e : φ = ψ)
    (N : DerivedCategory (ModuleCat.{u} S)) : (dext φ).obj N ⟶ (dext ψ).obj N :=
  eqToHom (congrArg (fun χ : S →+* T => (dext χ).obj N) e)

/-- A composition isomorphism followed by the inverse of another one with the same target, as a
composite of `dcomp` and a transport. -/
theorem compOfEq_trans_symm_hom_app (x : X →+* Y) (y : Y →+* Z) (x' : X →+* Y')
    (y' : Y' →+* Z) (p : X →+* Z) (hp : y.comp x = p) (hp' : y'.comp x' = p)
    (N : DerivedCategory (ModuleCat.{u} X)) :
    (totalDerivedExtensionScalarsCompOfEq x y p hp).hom.app N ≫
      (totalDerivedExtensionScalarsCompOfEq x' y' p hp').inv.app N =
      (dcomp x y).hom.app N ≫ dtr (hp.trans hp'.symm) N ≫ (dcomp x' y').inv.app N := by
  subst hp
  simp only [totalDerivedExtensionScalarsCompOfEq_hom_app, totalDerivedExtensionScalarsCompOfEq_inv_app,
    eqToHom_refl, Category.comp_id, Category.id_comp]

/-- **A step changing the first two maps of a triple composite.** -/
theorem leftStep (x : X →+* Y) (y : Y →+* Z) (x' : X →+* Y') (y' : Y' →+* Z) (z : Z →+* W)
    (e : y.comp x = y'.comp x') (N : DerivedCategory (ModuleCat.{u} X)) :
    (dext z).map ((dcomp x y).hom.app N ≫ dtr e N ≫ (dcomp x' y').inv.app N) ≫
        (dext z).map ((dcomp x' y').hom.app N) ≫ (dcomp (y'.comp x') z).hom.app N =
      (dext z).map ((dcomp x y).hom.app N) ≫ (dcomp (y.comp x) z).hom.app N ≫
        dtr (congrArg (fun φ : X →+* Z => z.comp φ) e) N := by
  rw [← CategoryTheory.Functor.map_comp_assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id, CategoryTheory.Functor.map_comp, Category.assoc]
  exact congrArg (fun t => (dext z).map ((dcomp x y).hom.app N) ≫ t)
    (map_eqToHom_comp_totalDerivedExtensionScalarsComp e z N)

/-- **A step changing the last two maps of a triple composite.** -/
theorem rightStep (x : X →+* Y) (y : Y →+* Z) (z : Z →+* W) (y' : Y →+* Z') (z' : Z' →+* W)
    (e : z.comp y = z'.comp y') (N : DerivedCategory (ModuleCat.{u} X)) :
    ((dcomp y z).hom.app ((dext x).obj N) ≫ dtr e ((dext x).obj N) ≫
        (dcomp y' z').inv.app ((dext x).obj N)) ≫
        (dcomp y' z').hom.app ((dext x).obj N) ≫ (dcomp x (z'.comp y')).hom.app N =
      (dcomp y z).hom.app ((dext x).obj N) ≫ (dcomp x (z.comp y)).hom.app N ≫
        dtr (congrArg (fun φ : Y →+* W => φ.comp x) e) N := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app_assoc]
  exact congrArg (fun t => (dcomp y z).hom.app ((dext x).obj N) ≫ t)
    (eqToHom_comp_totalDerivedExtensionScalarsComp x e N)

/-- The two normal forms of a triple composite agree. -/
theorem normalForm_assoc (x : X →+* Y) (y : Y →+* Z) (z : Z →+* W)
    (N : DerivedCategory (ModuleCat.{u} X)) :
    (dext z).map ((dcomp x y).hom.app N) ≫ (dcomp (y.comp x) z).hom.app N =
      (dcomp y z).hom.app ((dext x).obj N) ≫ (dcomp x (z.comp y)).hom.app N :=
  CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalarsComp_assoc.{u, u} x y z N

end Steps

/-! ### Coherence around a morphism of squares -/

section Cube

variable {R A R' A' R₁ A₁ R₁' A₁' : Type u} [CommRing R] [CommRing A] [CommRing R']
  [CommRing A'] [CommRing R₁] [CommRing A₁] [CommRing R₁'] [CommRing A₁']

/-- **The composition isomorphisms of derived extension of scalars around a morphism of
commutative squares of rings are coherent.** This is the hexagon condition of
`Stacks.CategoryTheory.BaseChange.map_transport` for the derived extension/restriction squares,
with every composite identified with derived extension of scalars along it. -/
theorem compOfEq_cube (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    (f₁ : R₁ →+* A₁) (g₁ : R₁ →+* R₁') (h₁ : A₁ →+* A₁') (i₁ : R₁' →+* A₁')
    (r : R →+* R₁) (a : A →+* A₁) (b : R' →+* R₁') (s : A' →+* A₁')
    (c₀ : R →+* A') (c₁ : R₁ →+* A₁') (pf : R →+* A₁) (pi : R' →+* A₁') (pg : R →+* R₁')
    (ph : A →+* A₁')
    (hf₀ : h.comp f = c₀) (hg₀ : i.comp g = c₀) (hf₁ : h₁.comp f₁ = c₁) (hg₁ : i₁.comp g₁ = c₁)
    (hpf : f₁.comp r = pf) (hpf' : a.comp f = pf) (hpi : i₁.comp b = pi) (hpi' : s.comp i = pi)
    (hpg : g₁.comp r = pg) (hpg' : b.comp g = pg) (hph : h₁.comp a = ph)
    (hph' : s.comp h = ph) (N : DerivedCategory (ModuleCat.{u} R)) :
    (dext i₁).map
        ((totalDerivedExtensionScalarsCompOfEq r g₁ pg hpg ≪≫
          (totalDerivedExtensionScalarsCompOfEq g b pg hpg').symm).hom.app N) ≫
      (totalDerivedExtensionScalarsCompOfEq b i₁ pi hpi ≪≫
          (totalDerivedExtensionScalarsCompOfEq i s pi hpi').symm).hom.app ((dext g).obj N) ≫
      (dext s).map ((totalDerivedExtensionScalarsCompOfEq g i c₀ hg₀).hom.app N ≫
          (totalDerivedExtensionScalarsCompOfEq f h c₀ hf₀).inv.app N) =
    (totalDerivedExtensionScalarsCompOfEq g₁ i₁ c₁ hg₁).hom.app ((dext r).obj N) ≫
      (totalDerivedExtensionScalarsCompOfEq f₁ h₁ c₁ hf₁).inv.app ((dext r).obj N) ≫
      (dext h₁).map
        ((totalDerivedExtensionScalarsCompOfEq r f₁ pf hpf ≪≫
          (totalDerivedExtensionScalarsCompOfEq f a pf hpf').symm).hom.app N) ≫
      (totalDerivedExtensionScalarsCompOfEq a h₁ ph hph ≪≫
          (totalDerivedExtensionScalarsCompOfEq h s ph hph').symm).hom.app ((dext f).obj N) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [compOfEq_trans_symm_hom_app r g₁ g b pg hpg hpg' N,
    compOfEq_trans_symm_hom_app b i₁ i s pi hpi hpi' ((dext g).obj N),
    compOfEq_trans_symm_hom_app g i f h c₀ hg₀ hf₀ N,
    reassoc_of% (compOfEq_trans_symm_hom_app g₁ i₁ f₁ h₁ c₁ hg₁ hf₁ ((dext r).obj N)),
    compOfEq_trans_symm_hom_app r f₁ f a pf hpf hpf' N,
    compOfEq_trans_symm_hom_app a h₁ h s ph hph hph' ((dext f).obj N)]
  let NF := (dext s).map ((dcomp f h).hom.app N) ≫ (dcomp (h.comp f) s).hom.app N
  haveI : IsIso NF := by dsimp only [NF]; infer_instance
  refine (cancel_mono NF).1 ?_
  -- both sides, followed by `NF`, are the normal form at `(r, g₁, i₁)` followed by a transport
  have hL := leftStep g i f h s (hg₀.trans hf₀.symm) N
  have hR2 := rightStep g b i₁ i s (hpi.trans hpi'.symm) N
  have hL3 := leftStep r g₁ g b i₁ (hpg.trans hpg'.symm) N
  have hR6 := rightStep f a h₁ h s (hph.trans hph'.symm) N
  have hL5 := leftStep r f₁ f a h₁ (hpf.trans hpf'.symm) N
  have hR4 := rightStep r g₁ i₁ f₁ h₁ (hg₁.trans hf₁.symm) N
  have a1 := normalForm_assoc g i s N
  have a2 := normalForm_assoc g b i₁ N
  have a3 := normalForm_assoc f h s N
  have a4 := normalForm_assoc f a h₁ N
  have a5 := normalForm_assoc r f₁ h₁ N
  have a6 := normalForm_assoc r g₁ i₁ N
  simp only [NF, Category.assoc] at hL hR2 hL3 hR6 hL5 hR4 ⊢
  rw [hL, reassoc_of% a1, reassoc_of% hR2, ← reassoc_of% a2, reassoc_of% hL3]
  rw [a3, hR6, ← reassoc_of% a4, reassoc_of% hL5, reassoc_of% a5,
    reassoc_of% hR4, ← reassoc_of% a6]
  simp only [dtr, eqToHom_trans]

end Cube

/-! ### Cohomology of the restriction isomorphism of a square -/

section RestrictSquareHomology

variable {R A R' A' : Type u} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']

/-- **The restriction isomorphism of a commutative square on cohomology** is the composite of the
cohomology comparisons of the four restrictions, followed by the identification of the two
restrictions of a module. -/
theorem homology_restrictSquareDerivedIso (f : R →+* A) (g : R →+* R') (h : A →+* A')
    (i : R' →+* A') (sq : h.comp f = i.comp g) (Z : DerivedCategory (ModuleCat.{u} A')) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map
          ((restrictSquareDerivedIso.{u, u, u, u, u} f g h i sq).hom.app Z) ≫
        ((ModuleCat.restrictScalars.{u} g).mapDerivedCategoryHomologyIso n).hom.app
          ((ModuleCat.restrictScalars.{u} i).mapDerivedCategory.obj Z) ≫
        (ModuleCat.restrictScalars.{u} g).map
          (((ModuleCat.restrictScalars.{u} i).mapDerivedCategoryHomologyIso n).hom.app Z) =
      ((ModuleCat.restrictScalars.{u} f).mapDerivedCategoryHomologyIso n).hom.app
          ((ModuleCat.restrictScalars.{u} h).mapDerivedCategory.obj Z) ≫
        (ModuleCat.restrictScalars.{u} f).map
          (((ModuleCat.restrictScalars.{u} h).mapDerivedCategoryHomologyIso n).hom.app Z) ≫
        (restrictSquareIso.{u, u, u, u, u} f g h i sq).hom.app
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj Z) := by
  let c := ComplexShape.up ℤ
  let rf := ModuleCat.restrictScalars.{u} f
  let rg := ModuleCat.restrictScalars.{u} g
  let rh := ModuleCat.restrictScalars.{u} h
  let ri := ModuleCat.restrictScalars.{u} i
  let HR := DerivedCategory.homologyFunctor (ModuleCat.{u} R) n
  let HA := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let HR' := DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let HA' := DerivedCategory.homologyFunctor (ModuleCat.{u} A') n
  let ιf := (rf.mapDerivedCategoryHomologyIso n).hom
  let ιg := (rg.mapDerivedCategoryHomologyIso n).hom
  let ιh := (rh.mapDerivedCategoryHomologyIso n).hom
  let ιi := (ri.mapDerivedCategoryHomologyIso n).hom
  let ρ := restrictSquareDerivedIso.{u, u, u, u, u} f g h i sq
  let τ := (restrictSquareIso.{u, u, u, u, u} f g h i sq).hom
  have hQ : ∀ L : CochainComplex (ModuleCat.{u} A') ℤ,
      HR.map (ρ.hom.app (DerivedCategory.Q.obj L)) ≫ ιg.app (ri.mapDerivedCategory.obj
          (DerivedCategory.Q.obj L)) ≫ rg.map (ιi.app (DerivedCategory.Q.obj L)) =
        ιf.app (rh.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≫
          rf.map (ιh.app (DerivedCategory.Q.obj L)) ≫ τ.app (HA'.obj (DerivedCategory.Q.obj L)) := by
    intro L
    let ff := rf.mapDerivedCategoryFactors
    let fg := rg.mapDerivedCategoryFactors
    let fh := rh.mapDerivedCategoryFactors
    let fi := ri.mapDerivedCategoryFactors
    let hR := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n
    let hA := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n
    let hR' := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R') n
    let hA' := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A') n
    let Lh := (rh.mapHomologicalComplex c).obj L
    let Li := (ri.mapHomologicalComplex c).obj L
    let HcR := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c n
    have hρ : ρ.hom.app (DerivedCategory.Q.obj L) =
        rf.mapDerivedCategory.map (fh.hom.app L) ≫ ff.hom.app Lh ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ c).app L) ≫
          fg.inv.app Li ≫ rg.mapDerivedCategory.map (fi.inv.app L) :=
      restrictSquareDerivedIso_hom_app_q_obj.{u, u, u, u, u} f g h i sq L
    have hf := Functor.mapDerivedCategoryHomologyIso_hom_app_Q
      rf n Lh
    have hg := Functor.mapDerivedCategoryHomologyIso_hom_app_Q
      rg n Li
    have hh := Functor.mapDerivedCategoryHomologyIso_hom_app_Q
      rh n L
    have hi := Functor.mapDerivedCategoryHomologyIso_hom_app_Q
      ri n L
    -- moving the comparisons of `h` and `i` inside
    have nf : ιf.app (rh.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) =
        HR.map (rf.mapDerivedCategory.map (fh.hom.app L)) ≫
          ιf.app (DerivedCategory.Q.obj Lh) ≫ rf.map (HA.map (fh.inv.app L)) := by
      have := ιf.naturality (fh.hom.app L)
      simp only [Functor.comp_map] at this
      rw [reassoc_of% this, ← rf.map_comp, ← HA.map_comp, Iso.hom_inv_id_app]
      exact ((congrArg (fun t => _ ≫ rf.map t) (HA.map_id _)).trans
        ((congrArg (fun t => _ ≫ t) (rf.map_id _)).trans (Category.comp_id _))).symm
    have ng : HR.map (rg.mapDerivedCategory.map (fi.inv.app L)) ≫ ιg.app (ri.mapDerivedCategory.obj
          (DerivedCategory.Q.obj L)) =
        ιg.app (DerivedCategory.Q.obj Li) ≫ rg.map (HR'.map (fi.inv.app L)) :=
      ιg.naturality (fi.inv.app L)
    have nτ : rf.map (rh.map (hA'.inv.app L)) ≫ τ.app (HA'.obj (DerivedCategory.Q.obj L)) =
        τ.app ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A') c n).obj L) ≫
          rg.map (ri.map (hA'.inv.app L)) :=
      τ.naturality (hA'.inv.app L)
    have nh : HR.map (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ c).app L)) ≫
          hR.hom.app ((rg.mapHomologicalComplex c).obj Li) =
        hR.hom.app ((rf.mapHomologicalComplex c).obj Lh) ≫
          HcR.map ((NatTrans.mapHomologicalComplex τ c).app L) :=
      hR.hom.naturality ((NatTrans.mapHomologicalComplex τ c).app L)
    have k1 := Stacks.ModulesOnACategory.TopCohomology.mapHomologicalComplexHomologyIso_hom_app_mapNatTrans
      (rh ⋙ rf) ri rg τ c n L
    have k2 := Stacks.ModulesOnACategory.TopCohomology.mapHomologicalComplexHomologyIso_hom_app_mapNatTrans
      (rh ⋙ rf) rh rf (𝟙 _) c n L
    rw [NatTrans.mapHomologicalComplex_id, NatTrans.id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, NatTrans.id_app] at k2
    replace k2 := k2.trans (Category.comp_id _)
    -- the homology comparison of a restricted complex is invertible
    have cancel : ∀ {S : Type u} [CommRing S] (φ : S →+* A')
        (F : ModuleCat.{u} S ⥤ ModuleCat.{u} R),
        F.map ((DerivedCategory.homologyFunctorFactors (ModuleCat S) n).inv.app
            (((ModuleCat.restrictScalars φ).mapHomologicalComplex c).obj L)) ≫
          F.map ((DerivedCategory.homologyFunctor (ModuleCat S) n).map
            ((ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.inv.app L)) ≫
          F.map ((DerivedCategory.homologyFunctor (ModuleCat S) n).map
            ((ModuleCat.restrictScalars φ).mapDerivedCategoryFactors.hom.app L)) ≫
          F.map ((DerivedCategory.homologyFunctorFactors (ModuleCat S) n).hom.app
            (((ModuleCat.restrictScalars φ).mapHomologicalComplex c).obj L)) = 𝟙 _ := by
      intro S _ φ F
      rw [← F.map_comp, ← F.map_comp, ← F.map_comp, ← (DerivedCategory.homologyFunctor
        (ModuleCat S) n).map_comp_assoc, Iso.inv_hom_id_app]
      refine (congrArg F.map ((congrArg (fun t => _ ≫ t ≫ _)
        (CategoryTheory.Functor.map_id _ _)).trans ?_)).trans (F.map_id _)
      exact (congrArg (fun t => _ ≫ t) (Category.id_comp _)).trans (Iso.inv_hom_id_app _ _)
    -- left-hand side
    have eL : HR.map (ρ.hom.app (DerivedCategory.Q.obj L)) ≫ ιg.app (ri.mapDerivedCategory.obj
          (DerivedCategory.Q.obj L)) ≫ rg.map (ιi.app (DerivedCategory.Q.obj L)) =
        HR.map (rf.mapDerivedCategory.map (fh.hom.app L)) ≫ HR.map (ff.hom.app Lh) ≫
          hR.hom.app ((rf.mapHomologicalComplex c).obj Lh) ≫
          (HcR.map ((NatTrans.mapHomologicalComplex τ c).app L) ≫
            (rg.mapHomologicalComplexHomologyIso c n).hom.app Li ≫
            rg.map ((ri.mapHomologicalComplexHomologyIso c n).hom.app L)) ≫
          rg.map (ri.map (hA'.inv.app L)) := by
      rw [hρ, hi]
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% ng, hg]
      simp only [Category.assoc]
      have c1 : HR.map (fg.inv.app Li) ≫
          (DerivedCategory.homologyFunctor (ModuleCat R) n).map
            (rg.mapDerivedCategoryFactors.hom.app Li) = 𝟙 _ := by
        rw [← HR.map_comp, Iso.inv_hom_id_app]
        exact HR.map_id _
      rw [reassoc_of% c1, reassoc_of% (cancel i rg), reassoc_of% nh]
    -- right-hand side
    have eR : ιf.app (rh.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≫
          rf.map (ιh.app (DerivedCategory.Q.obj L)) ≫ τ.app (HA'.obj (DerivedCategory.Q.obj L)) =
        HR.map (rf.mapDerivedCategory.map (fh.hom.app L)) ≫ HR.map (ff.hom.app Lh) ≫
          hR.hom.app ((rf.mapHomologicalComplex c).obj Lh) ≫
          ((rf.mapHomologicalComplexHomologyIso c n).hom.app Lh ≫
            rf.map ((rh.mapHomologicalComplexHomologyIso c n).hom.app L)) ≫
          rf.map (rh.map (hA'.inv.app L)) ≫ τ.app (HA'.obj (DerivedCategory.Q.obj L)) := by
      rw [nf, hf, hh]
      simp only [Functor.map_comp, Category.assoc]
      rw [reassoc_of% (cancel h rf)]
    rw [eL, eR, k1, ← reassoc_of% k2, nτ]
    simp only [Category.assoc]
    rfl
  -- from complexes to arbitrary objects
  let e := DerivedCategory.Q.objObjPreimageIso Z
  let L := DerivedCategory.Q.objPreimage Z
  have hiso : IsIso (HR.map ((rh.mapDerivedCategory ⋙ rf.mapDerivedCategory).map e.hom)) :=
    inferInstance
  refine (cancel_epi (HR.map ((rh.mapDerivedCategory ⋙ rf.mapDerivedCategory).map e.hom))).1 ?_
  have hL : HR.map ((rh.mapDerivedCategory ⋙ rf.mapDerivedCategory).map e.hom) ≫
      HR.map (ρ.hom.app Z) ≫ ιg.app (ri.mapDerivedCategory.obj Z) ≫ rg.map (ιi.app Z) =
      (HR.map (ρ.hom.app (DerivedCategory.Q.obj L)) ≫ ιg.app (ri.mapDerivedCategory.obj
          (DerivedCategory.Q.obj L)) ≫ rg.map (ιi.app (DerivedCategory.Q.obj L))) ≫
        rg.map (ri.map (HA'.map e.hom)) := by
    have h1 := ρ.hom.naturality e.hom
    have h2 := ιg.naturality (ri.mapDerivedCategory.map e.hom)
    have h3 := ιi.naturality e.hom
    simp only [Functor.comp_map] at h1 h2 h3 ⊢
    rw [← HR.map_comp_assoc, h1, HR.map_comp, Category.assoc, reassoc_of% h2, ← rg.map_comp, h3,
      rg.map_comp]
    simp only [Category.assoc]
    rfl
  have hR : HR.map ((rh.mapDerivedCategory ⋙ rf.mapDerivedCategory).map e.hom) ≫
      ιf.app (rh.mapDerivedCategory.obj Z) ≫ rf.map (ιh.app Z) ≫ τ.app (HA'.obj Z) =
      (ιf.app (rh.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≫
          rf.map (ιh.app (DerivedCategory.Q.obj L)) ≫ τ.app (HA'.obj (DerivedCategory.Q.obj L))) ≫
        rg.map (ri.map (HA'.map e.hom)) := by
    have h1 := ιf.naturality (rh.mapDerivedCategory.map e.hom)
    have h2 := ιh.naturality e.hom
    have h3 := τ.naturality (HA'.map e.hom)
    simp only [Functor.comp_map] at h1 h2 h3 ⊢
    rw [reassoc_of% h1, ← rf.map_comp_assoc, h2, rf.map_comp, Category.assoc, h3]
    simp only [Category.assoc]
    rfl
  exact hL.trans ((congrArg (fun t => t ≫ rg.map (ri.map (HA'.map e.hom))) (hQ L)).trans hR.symm)

/-- **The unit form of the base change map of Stacks 065Z.** For a commutative square of ring
homomorphisms, the unit along `g` at `K|_R`, followed by the restriction of the base change map,
is the restriction of the unit along `h`, followed by the restriction isomorphism of the
square. -/
theorem unit_comp_baseChangeMap (f : R →+* A) (g : R →+* R') (h : A →+* A') (i : R' →+* A')
    (c : R →+* A') (h₁ : h.comp f = c) (h₂ : i.comp g = c)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (totalDerivedExtensionScalarsAdjunction g).unit.app
        ((ModuleCat.restrictScalars f).mapDerivedCategory.obj K) ≫
      (ModuleCat.restrictScalars g).mapDerivedCategory.map
        (Stacks.CategoryTheory.BaseChange.map (totalDerivedExtensionScalarsAdjunction f)
          (totalDerivedExtensionScalarsAdjunction i) (totalDerivedExtensionScalarsCompOfEq g i c h₂)
          (totalDerivedExtensionScalarsCompOfEq f h c h₁) K) =
    (ModuleCat.restrictScalars f).mapDerivedCategory.map
        ((totalDerivedExtensionScalarsAdjunction h).unit.app K) ≫
      (restrictSquareDerivedIso.{u, u, u, u, u} f g h i (h₁.trans h₂.symm)).hom.app
        ((dext h).obj K) := by
  let Tg := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} g
  let Th := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} h
  rw [← ringHomSquareComparison_app_eq_map f g h i c h₁ h₂ K]
  haveI : (ModuleCat.extendScalars.{u, u, u} g).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u} g).isLeftAdjoint
  haveI : (ModuleCat.extendScalars.{u, u, u} h).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{u} h).isLeftAdjoint
  let cg : DerivedCategory.Q ⋙ Tg.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := Tg.comparison
  let ch : DerivedCategory.Q ⋙ Th.functor ⟶
      (ModuleCat.extendScalars.{u, u, u} h).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q := Th.comparison
  haveI : Tg.functor.IsLeftDerivedFunctor cg
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) := Tg.isLeftDerived
  haveI : Th.functor.IsLeftDerivedFunctor ch
      (HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)) := Th.isLeftDerived
  exact unit_comp_derivedBaseChangeComparison.{u, u, u, u, u} f g h i (h₁.trans h₂.symm)
    Tg.functor Th.functor cg ch K

end RestrictSquareHomology

/-! ### The map induced on cohomology by a morphism of squares -/

section SecondSquare

variable {R A R' A' R₁ A₁ R₁' A₁' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [CommRing R₁] [CommRing A₁] [CommRing R₁'] [CommRing A₁']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']
  [Algebra R₁ A₁] [Algebra R₁ R₁'] [Algebra R₁ A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁']
  [IsScalarTower R₁ A₁ A₁'] [IsScalarTower R₁ R₁' A₁']
  [Algebra R R₁] [Algebra A A₁] [Algebra R' R₁'] [Algebra A' A₁']
  [Algebra R A₁] [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁]
  [Algebra R R₁'] [IsScalarTower R R' R₁'] [IsScalarTower R R₁ R₁']
  [Algebra A A₁'] [IsScalarTower A A' A₁'] [IsScalarTower A A₁ A₁']
  [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']

omit [Algebra R A'] [Algebra R₁ A₁'] [IsScalarTower R₁ A₁ A₁'] [IsScalarTower R₁ R₁' A₁']
  [IsScalarTower R A A'] [IsScalarTower R R' A'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra A' A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [Algebra A A'] [Algebra R' A'] in
/-- The square `R → A → A₁`, `R → R₁ → A₁` commutes. -/
theorem squareRA₁ :
    (algebraMap A A₁).comp (algebraMap R A) = (algebraMap R₁ A₁).comp (algebraMap R R₁) :=
  (IsScalarTower.algebraMap_eq R A A₁).symm.trans (IsScalarTower.algebraMap_eq R R₁ A₁)

/-- **The map on derived base changes induced by a morphism of squares.** For `K ∈ D(A)`, the
morphism `K|_R ⊗ᴸ_R R' ⟶ ((K ⊗ᴸ_A A₁)|_{R₁} ⊗ᴸ_{R₁} R₁')|_{R'}` of `D(R')`: derived base change
along `R → R'` of the restriction of the unit `K ⟶ (K ⊗ᴸ_A A₁)|_A`, followed by the comparison
of Stacks 065Z for the square `R → R₁`, `R → R'`, `R₁ → R₁'`, `R' → R₁'`. -/
def secondSquareDerivedMap (K : DerivedCategory (ModuleCat.{u} A)) :
    (dext (algebraMap R R')).obj ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) ⟶
      (ModuleCat.restrictScalars (algebraMap R' R₁')).mapDerivedCategory.obj
        ((dext (algebraMap R₁ R₁')).obj
          ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.obj
            ((dext (algebraMap A A₁)).obj K))) :=
  (dext (algebraMap R R')).map
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsAdjunction (algebraMap A A₁)).unit.app K) ≫
        (restrictSquareDerivedIso.{u, u, u, u, u} (algebraMap R A) (algebraMap R R₁)
          (algebraMap A A₁) (algebraMap R₁ A₁) squareRA₁).hom.app
            ((dext (algebraMap A A₁)).obj K)) ≫
    (squareDerivedComparison (R := R) (A := R₁) (R' := R') (A' := R₁')).app
      ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.obj
        ((dext (algebraMap A A₁)).obj K))

/-- The comparison of Stacks 065Z for the square `R → A`, `R → R₁`, `A → A₁`, `R₁ → A₁`, as a
base change map. -/
abbrev leftSquareMap (K : DerivedCategory (ModuleCat.{u} A)) :
    (dext (algebraMap R R₁)).obj
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) ⟶
      (ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.obj
        ((dext (algebraMap A A₁)).obj K) :=
  Stacks.CategoryTheory.BaseChange.map (totalDerivedExtensionScalarsAdjunction (algebraMap R A))
    (totalDerivedExtensionScalarsAdjunction (algebraMap R₁ A₁))
    (totalDerivedExtensionScalarsCompOfEq (algebraMap R R₁) (algebraMap R₁ A₁) (algebraMap R A₁)
      (IsScalarTower.algebraMap_eq R R₁ A₁).symm)
    (totalDerivedExtensionScalarsCompOfEq (algebraMap R A) (algebraMap A A₁) (algebraMap R A₁)
      (IsScalarTower.algebraMap_eq R A A₁).symm) K

omit [Algebra R A'] [Algebra R₁ A₁'] [IsScalarTower R₁ A₁ A₁'] [IsScalarTower R₁ R₁' A₁']
  [IsScalarTower R A A'] [IsScalarTower R R' A'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra A' A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [Algebra A A'] [Algebra R' A'] in
/-- The unit form of `leftSquareMap`: the unit along `R → R₁` followed by its restriction is the
restriction of the unit along `A → A₁`. -/
theorem unit_comp_leftSquareMap (K : DerivedCategory (ModuleCat.{u} A)) :
    (totalDerivedExtensionScalarsAdjunction (algebraMap R R₁)).unit.app
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K) ≫
      (ModuleCat.restrictScalars (algebraMap R R₁)).mapDerivedCategory.map
        (leftSquareMap (R₁ := R₁) K) =
    (ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map
        ((totalDerivedExtensionScalarsAdjunction (algebraMap A A₁)).unit.app K) ≫
      (restrictSquareDerivedIso.{u, u, u, u, u} (algebraMap R A) (algebraMap R R₁)
        (algebraMap A A₁) (algebraMap R₁ A₁) squareRA₁).hom.app
          ((dext (algebraMap A A₁)).obj K) :=
  unit_comp_baseChangeMap (algebraMap R A) (algebraMap R R₁) (algebraMap A A₁)
    (algebraMap R₁ A₁) (algebraMap R A₁) (IsScalarTower.algebraMap_eq R A A₁).symm
    (IsScalarTower.algebraMap_eq R R₁ A₁).symm K

/-- The square `R' → A' → A₁'`, `R' → R₁' → A₁'` commutes. -/
theorem squareR'A₁' :
    (algebraMap A' A₁').comp (algebraMap R' A') = (algebraMap R₁' A₁').comp (algebraMap R' R₁') :=
  (IsScalarTower.algebraMap_eq R' A' A₁').symm.trans (IsScalarTower.algebraMap_eq R' R₁' A₁')

/-- **The map induced by a morphism of squares, against the comparison of the second square.**
`secondSquareDerivedMap` followed by the comparison of Stacks 065Z of the second square at
`K ⊗ᴸ_A A₁` is the comparison of the first square at `K`, followed by the unit along `A' → A₁'`,
the restriction isomorphism of the square `R' → A' → A₁'`, `R' → R₁' → A₁'`, and the
composition isomorphisms. -/
theorem secondSquareDerivedMap_comp (K : DerivedCategory (ModuleCat.{u} A)) :
    secondSquareDerivedMap (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K ≫
        (ModuleCat.restrictScalars (algebraMap R' R₁')).mapDerivedCategory.map
          ((squareDerivedComparison (R := R₁) (A := A₁) (R' := R₁') (A' := A₁')).app
            ((dext (algebraMap A A₁)).obj K)) =
      (squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app K ≫
        (ModuleCat.restrictScalars (algebraMap R' A')).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsAdjunction (algebraMap A' A₁')).unit.app
            ((dext (algebraMap A A')).obj K)) ≫
        (restrictSquareDerivedIso.{u, u, u, u, u} (algebraMap R' A') (algebraMap R' R₁')
          (algebraMap A' A₁') (algebraMap R₁' A₁') squareR'A₁').hom.app
            ((dext (algebraMap A' A₁')).obj ((dext (algebraMap A A')).obj K)) ≫
        (ModuleCat.restrictScalars (algebraMap R' R₁')).mapDerivedCategory.map
          ((ModuleCat.restrictScalars (algebraMap R₁' A₁')).mapDerivedCategory.map
            ((totalDerivedExtensionScalarsCompOfEq (algebraMap A A') (algebraMap A' A₁')
                (algebraMap A A₁') (IsScalarTower.algebraMap_eq A A' A₁').symm).hom.app K ≫
              (totalDerivedExtensionScalarsCompOfEq (algebraMap A A₁) (algebraMap A₁ A₁')
                (algebraMap A A₁') (IsScalarTower.algebraMap_eq A A₁ A₁').symm).inv.app K)) := by
  let f := algebraMap R A
  let g := algebraMap R R'
  let h := algebraMap A A'
  let i := algebraMap R' A'
  let f₁ := algebraMap R₁ A₁
  let g₁ := algebraMap R₁ R₁'
  let h₁ := algebraMap A₁ A₁'
  let i₁ := algebraMap R₁' A₁'
  let r := algebraMap R R₁
  let a := algebraMap A A₁
  let b := algebraMap R' R₁'
  let s := algebraMap A' A₁'
  let adj := fun {X Y : Type u} [CommRing X] [CommRing Y] (φ : X →+* Y) =>
    totalDerivedExtensionScalarsAdjunction φ
  let X := (ModuleCat.restrictScalars f).mapDerivedCategory.obj K
  let K₁ := (dext a).obj K
  let Y := (ModuleCat.restrictScalars f₁).mapDerivedCategory.obj K₁
  let Rb := (ModuleCat.restrictScalars.{u} b).mapDerivedCategory
  let Ri := (ModuleCat.restrictScalars.{u} i).mapDerivedCategory
  let Ri₁ := (ModuleCat.restrictScalars.{u} i₁).mapDerivedCategory
  -- the composition isomorphisms
  let pf := algebraMap R A₁
  let pg := algebraMap R R₁'
  let pi := algebraMap R' A₁'
  let ph := algebraMap A A₁'
  let c₀ := algebraMap R A'
  let c₁ := algebraMap R₁ A₁'
  let egr := totalDerivedExtensionScalarsCompOfEq g i c₀ (IsScalarTower.algebraMap_eq R R' A').symm
  let efr := totalDerivedExtensionScalarsCompOfEq f h c₀ (IsScalarTower.algebraMap_eq R A A').symm
  let eg := totalDerivedExtensionScalarsCompOfEq g₁ i₁ c₁
    (IsScalarTower.algebraMap_eq R₁ R₁' A₁').symm
  let ef := totalDerivedExtensionScalarsCompOfEq f₁ h₁ c₁
    (IsScalarTower.algebraMap_eq R₁ A₁ A₁').symm
  let βf := totalDerivedExtensionScalarsCompOfEq r f₁ pf (IsScalarTower.algebraMap_eq R R₁ A₁).symm ≪≫
    (totalDerivedExtensionScalarsCompOfEq f a pf (IsScalarTower.algebraMap_eq R A A₁).symm).symm
  let βf' := totalDerivedExtensionScalarsCompOfEq b i₁ pi
      (IsScalarTower.algebraMap_eq R' R₁' A₁').symm ≪≫
    (totalDerivedExtensionScalarsCompOfEq i s pi (IsScalarTower.algebraMap_eq R' A' A₁').symm).symm
  let βg := totalDerivedExtensionScalarsCompOfEq r g₁ pg
      (IsScalarTower.algebraMap_eq R R₁ R₁').symm ≪≫
    (totalDerivedExtensionScalarsCompOfEq g b pg (IsScalarTower.algebraMap_eq R R' R₁').symm).symm
  let βg' := totalDerivedExtensionScalarsCompOfEq a h₁ ph
      (IsScalarTower.algebraMap_eq A A₁ A₁').symm ≪≫
    (totalDerivedExtensionScalarsCompOfEq h s ph (IsScalarTower.algebraMap_eq A A' A₁').symm).symm
  have hhex : ∀ N, (dext i₁).map (βg.hom.app N) ≫ βf'.hom.app ((dext g).obj N) ≫
      (dext s).map (egr.hom.app N ≫ efr.inv.app N) =
      eg.hom.app ((dext r).obj N) ≫ ef.inv.app ((dext r).obj N) ≫ (dext h₁).map (βf.hom.app N) ≫
        βg'.hom.app ((dext f).obj N) := fun N =>
    compOfEq_cube f g h i f₁ g₁ h₁ i₁ r a b s c₀ c₁ pf pi pg ph _ _ _ _ _ _ _ _ _ _ _ _ N
  have hT := Stacks.CategoryTheory.BaseChange.map_transport (adj f) (adj i) egr efr (adj f₁)
    (adj i₁) eg ef (dext r) (dext a) (dext b) (dext s) βf βf' βg βg' hhex K
  -- the two transport units are base change maps
  let tU := leftSquareMap (R := R) (A := A) (R₁ := R₁) (A₁ := A₁) K
  have htU : Stacks.CategoryTheory.BaseChange.transportUnit (adj f) (adj f₁) (dext r) (dext a) βf K =
      tU := by
    simp only [tU, leftSquareMap, Stacks.CategoryTheory.BaseChange.map_eq,
      Stacks.CategoryTheory.BaseChange.transportUnit, βf, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc]
    rfl
  let tU' := Stacks.CategoryTheory.BaseChange.map (adj i) (adj i₁)
    (totalDerivedExtensionScalarsCompOfEq b i₁ pi (IsScalarTower.algebraMap_eq R' R₁' A₁').symm)
    (totalDerivedExtensionScalarsCompOfEq i s pi (IsScalarTower.algebraMap_eq R' A' A₁').symm)
    ((dext h).obj K)
  have htU' : Stacks.CategoryTheory.BaseChange.transportUnit (adj i) (adj i₁) (dext b) (dext s) βf'
      ((dext h).obj K) = tU' := by
    simp only [tU', Stacks.CategoryTheory.BaseChange.map_eq,
      Stacks.CategoryTheory.BaseChange.transportUnit, βf', Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc]
  have hu' := unit_comp_baseChangeMap i b s i₁ pi (IsScalarTower.algebraMap_eq R' A' A₁').symm
    (IsScalarTower.algebraMap_eq R' R₁' A₁').symm ((dext h).obj K)
  -- the comparisons of the two squares are base change maps
  have h0 := squareDerivedComparison_app_eq_map (R := R) (A := A) (R' := R') (A' := A') K
  have h1 := squareDerivedComparison_app_eq_map (R := R₁) (A := A₁) (R' := R₁') (A' := A₁') K₁
  -- `secondSquareDerivedMap` in transport form
  have hR := squareDerivedComparison_app_eq_map (R := R) (A := R₁) (R' := R') (A' := R₁')
  have key : secondSquareDerivedMap (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K =
      (adj b).unit.app ((dext g).obj X) ≫ Rb.map (βg.inv.app X ≫ (dext g₁).map tU) := by
    have hn : (dext g).map ((ModuleCat.restrictScalars r).mapDerivedCategory.map tU) ≫
        (squareDerivedComparison (R := R) (A := R₁) (R' := R') (A' := R₁')).app Y =
        (squareDerivedComparison (R := R) (A := R₁) (R' := R') (A' := R₁')).app ((dext r).obj X) ≫
          Rb.map ((dext g₁).map tU) :=
      (squareDerivedComparison (R := R) (A := R₁) (R' := R') (A' := R₁')).naturality tU
    have hu := Stacks.CategoryTheory.BaseChange.unit_comp_map (adj r) (adj b)
      (totalDerivedExtensionScalarsCompOfEq g b pg (IsScalarTower.algebraMap_eq R R' R₁').symm)
      (totalDerivedExtensionScalarsCompOfEq r g₁ pg (IsScalarTower.algebraMap_eq R R₁ R₁').symm) X
    rw [← hR] at hu
    simp only [secondSquareDerivedMap, ← unit_comp_leftSquareMap, CategoryTheory.Functor.map_comp,
      Category.assoc]
    rw [hn, reassoc_of% hu]
    simp only [βg, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, CategoryTheory.Functor.map_comp,
      Category.assoc]
    rfl
  rw [key, h0, h1, Category.assoc, ← Rb.map_comp]
  rw [htU, htU'] at hT
  have hη := (adj b).unit.naturality
    (Stacks.CategoryTheory.BaseChange.map (adj f) (adj i) egr efr K)
  simp only [Functor.comp_map, Functor.id_map] at hη
  rw [Category.assoc, hT, Iso.inv_hom_id_app_assoc, CategoryTheory.Functor.map_comp,
    ← reassoc_of% hη, CategoryTheory.Functor.map_comp, reassoc_of% hu']
  simp only [βg', Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
  rfl

omit [Algebra R A'] [Algebra R₁ A₁'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [IsScalarTower R₁ A₁ A₁'] [IsScalarTower R₁ R₁' A₁'] [Algebra R R₁'] [IsScalarTower R R' R₁']
  [IsScalarTower R R₁ R₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra R A₁] [IsScalarTower R A A₁] [IsScalarTower R R₁ A₁] [Algebra R₁ A₁] [Algebra R₁ R₁']
  [Algebra R R₁] [Algebra R' R₁'] [Algebra R A] [Algebra R R'] [Algebra R' A'] in
/-- The composition isomorphisms followed by `extendScalarsBaseChangeHom` are derived base change
of `φ`. -/
theorem compOfEq_comp_extendScalarsBaseChangeHom (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (dext (algebraMap A A')).obj K ⟶ K') :
    (totalDerivedExtensionScalarsCompOfEq (algebraMap A A') (algebraMap A' A₁')
        (algebraMap A A₁') (IsScalarTower.algebraMap_eq A A' A₁').symm).hom.app K ≫
      (totalDerivedExtensionScalarsCompOfEq (algebraMap A A₁) (algebraMap A₁ A₁')
        (algebraMap A A₁') (IsScalarTower.algebraMap_eq A A₁ A₁').symm).inv.app K ≫
      extendScalarsBaseChangeHom (A₁ := A₁) (A₁' := A₁') K K' φ =
    (dext (algebraMap A' A₁')).map φ := by
  rw [extendScalarsBaseChangeHom_eq, totalDerivedExtensionScalarsCompOfEq_hom_app,
    totalDerivedExtensionScalarsCompOfEq_inv_app]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.hom_inv_id_app_assoc]

omit [Algebra R A'] [Algebra R₁ A₁'] [IsScalarTower R A A'] [IsScalarTower R R' A']
  [IsScalarTower R₁ A₁ A₁'] [IsScalarTower R₁ R₁' A₁'] [Algebra A A₁'] [IsScalarTower A A' A₁']
  [IsScalarTower A A₁ A₁'] [Algebra R' A₁'] [IsScalarTower R' A' A₁'] [IsScalarTower R' R₁' A₁']
  [Algebra A' A₁'] [Algebra A₁ A₁'] [Algebra R₁' A₁'] [Algebra A A'] [Algebra R' A'] in
/-- `secondSquareDerivedMap` is natural in `K`. -/
theorem secondSquareDerivedMap_naturality {K L : DerivedCategory (ModuleCat.{u} A)} (u : K ⟶ L) :
    (dext (algebraMap R R')).map ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map u) ≫
        secondSquareDerivedMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') L =
      secondSquareDerivedMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K ≫
        (ModuleCat.restrictScalars (algebraMap R' R₁')).mapDerivedCategory.map
          ((dext (algebraMap R₁ R₁')).map
            ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.map
              ((dext (algebraMap A A₁)).map u))) := by
  let Rf := (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory
  let Rf₁ := (ModuleCat.restrictScalars.{u} (algebraMap R₁ A₁)).mapDerivedCategory
  let Rr := (ModuleCat.restrictScalars.{u} (algebraMap R R₁)).mapDerivedCategory
  let Ra := (ModuleCat.restrictScalars.{u} (algebraMap A A₁)).mapDerivedCategory
  let η := (totalDerivedExtensionScalarsAdjunction (algebraMap A A₁)).unit
  let ρ := restrictSquareDerivedIso.{u, u, u, u, u} (algebraMap R A) (algebraMap R R₁)
    (algebraMap A A₁) (algebraMap R₁ A₁) squareRA₁
  let τ := squareDerivedComparison (R := R) (A := R₁) (R' := R') (A' := R₁')
  have h1 : u ≫ η.app L = η.app K ≫ Ra.map ((dext (algebraMap A A₁)).map u) := η.naturality u
  have h2 : Rf.map (Ra.map ((dext (algebraMap A A₁)).map u)) ≫ ρ.hom.app ((dext (algebraMap A A₁)).obj L) =
      ρ.hom.app ((dext (algebraMap A A₁)).obj K) ≫ Rr.map (Rf₁.map ((dext (algebraMap A A₁)).map u)) :=
    ρ.hom.naturality ((dext (algebraMap A A₁)).map u)
  have h3 : (dext (algebraMap R R')).map (Rr.map (Rf₁.map ((dext (algebraMap A A₁)).map u))) ≫
      τ.app (Rf₁.obj ((dext (algebraMap A A₁)).obj L)) =
      τ.app (Rf₁.obj ((dext (algebraMap A A₁)).obj K)) ≫
        (ModuleCat.restrictScalars (algebraMap R' R₁')).mapDerivedCategory.map
          ((dext (algebraMap R₁ R₁')).map (Rf₁.map ((dext (algebraMap A A₁)).map u))) :=
    τ.naturality (Rf₁.map ((dext (algebraMap A A₁)).map u))
  have h12 : Rf.map u ≫ Rf.map (η.app L) ≫ ρ.hom.app ((dext (algebraMap A A₁)).obj L) =
      (Rf.map (η.app K) ≫ ρ.hom.app ((dext (algebraMap A A₁)).obj K)) ≫
        Rr.map (Rf₁.map ((dext (algebraMap A A₁)).map u)) := by
    rw [← Rf.map_comp_assoc, h1, Rf.map_comp, Category.assoc, h2, Category.assoc]
  simp only [secondSquareDerivedMap]
  rw [← CategoryTheory.Functor.map_comp_assoc, h12, CategoryTheory.Functor.map_comp,
    Category.assoc, Category.assoc]
  exact congrArg (fun t => _ ≫ t) h3

/-- **The map induced on cohomology by a morphism of squares.** The `R'`-linear map
`Hⁿ(K|_R ⊗ᴸ_R R') ⟶ Hⁿ((K ⊗ᴸ_A A₁)|_{R₁} ⊗ᴸ_{R₁} R₁')` induced by `secondSquareDerivedMap`. -/
def secondSquareHomologyMap (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    baseChangeCohomologyOverBase (R := R) (R' := R') K n ⟶
      (ModuleCat.restrictScalars (algebraMap R' R₁')).obj
        (baseChangeCohomologyOverBase (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n) :=
  (DerivedCategory.homologyFunctor (ModuleCat.{u} R') n).map
      (secondSquareDerivedMap (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K) ≫
    ((ModuleCat.restrictScalars (algebraMap R' R₁')).mapDerivedCategoryHomologyIso n).hom.app _

/-- `secondSquareHomologyMap` carries the action of `a ∈ A` to the action of its image in `A₁`. -/
theorem secondSquareHomologyMap_action (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (a : A)
    (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    (secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n).hom
        (baseChangeCohomologyAction (R := R) (R' := R') K n a m) =
      baseChangeCohomologyAction (R := R₁) (R' := R₁') ((dext (algebraMap A A₁)).obj K) n
        (algebraMap A A₁ a)
        ((secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n).hom m) := by
  let HR' := DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let HR₁' := DerivedCategory.homologyFunctor (ModuleCat.{u} R₁') n
  let rb := ModuleCat.restrictScalars.{u} (algebraMap R' R₁')
  let ιb := (rb.mapDerivedCategoryHomologyIso n).hom
  let Z := (dext (algebraMap R₁ R₁')).map ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.map
    ((dext (algebraMap A A₁)).map (a • 𝟙 K)))
  have hnat := secondSquareDerivedMap_naturality (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁)
    (R₁' := R₁') (a • 𝟙 K)
  have hι := ιb.naturality Z
  have hsc : (dext (algebraMap A A₁)).map (a • 𝟙 K) =
      algebraMap A A₁ a • 𝟙 ((dext (algebraMap A A₁)).obj K) :=
    derivedExtension_scalar (algebraMap A A₁) a K
  have hM : (HR'.map ((dext (algebraMap R R')).map
        ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.map (a • 𝟙 K)))) ≫
      secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n =
      secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n ≫
        rb.map (HR₁'.map Z) := by
    simp only [Functor.comp_map] at hι
    simp only [secondSquareHomologyMap]
    rw [← HR'.map_comp_assoc, hnat, HR'.map_comp, Category.assoc, hι]
    rfl
  have h := congrArg (fun t => t.hom m) hM
  refine h.trans ?_
  exact congrArg (fun t => (HR₁'.map ((dext (algebraMap R₁ R₁')).map
    ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.map t))).hom
      (show HR₁'.obj ((dext (algebraMap R₁ R₁')).obj
          ((ModuleCat.restrictScalars (algebraMap R₁ A₁)).mapDerivedCategory.obj
            ((dext (algebraMap A A₁)).obj K))) from
        (secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n).hom m))
    hsc

/-- **Naturality (N) of the base-change comparison in the square.** For `φ : K ⊗ᴸ_A A' ⟶ K'`, the
comparison of the second square at `K ⊗ᴸ_A A₁`, `K' ⊗ᴸ_{A'} A₁'` and
`extendScalarsBaseChangeHom φ`, after `secondSquareHomologyMap`, is the comparison of the first
square followed by the unit `Hⁿ(K') ⟶ Hⁿ(K' ⊗ᴸ_{A'} A₁')`. -/
theorem cohomologyComparisonMap_secondSquare (K : DerivedCategory (ModuleCat.{u} A))
    (K' : DerivedCategory (ModuleCat.{u} A')) (φ : (dext (algebraMap A A')).obj K ⟶ K') (n : ℤ)
    (m : baseChangeCohomologyOverBase (R := R) (R' := R') K n) :
    (cohomologyComparisonMap (R := R₁) (A := A₁) (R' := R₁') (A' := A₁')
        ((dext (algebraMap A A₁)).obj K) ((dext (algebraMap A' A₁')).obj K')
        (extendScalarsBaseChangeHom K K' φ) n).hom
      ((secondSquareHomologyMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K n).hom m) =
    (derivedUnitHomologyMap (T := A₁') K' n).hom
      ((cohomologyComparisonMap (R := R) (R' := R') K K' φ n).hom m) := by
  let HR' := DerivedCategory.homologyFunctor (ModuleCat.{u} R') n
  let HR₁' := DerivedCategory.homologyFunctor (ModuleCat.{u} R₁') n
  let HA' := DerivedCategory.homologyFunctor (ModuleCat.{u} A') n
  let HA₁' := DerivedCategory.homologyFunctor (ModuleCat.{u} A₁') n
  let rb := ModuleCat.restrictScalars.{u} (algebraMap R' R₁')
  let ri := ModuleCat.restrictScalars.{u} (algebraMap R' A')
  let ri₁ := ModuleCat.restrictScalars.{u} (algebraMap R₁' A₁')
  let rs := ModuleCat.restrictScalars.{u} (algebraMap A' A₁')
  let ιb := (rb.mapDerivedCategoryHomologyIso n).hom
  let ιi := (ri.mapDerivedCategoryHomologyIso n).hom
  let ιi₁ := (ri₁.mapDerivedCategoryHomologyIso n).hom
  let ιs := (rs.mapDerivedCategoryHomologyIso n).hom
  let K₁' := (dext (algebraMap A' A₁')).obj K'
  let τ₀ := (squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')).app K
  let τ₁ := (squareDerivedComparison (R := R₁) (A := A₁) (R' := R₁') (A' := A₁')).app
    ((dext (algebraMap A A₁)).obj K)
  let ψ := secondSquareDerivedMap (R := R) (R' := R') (R₁ := R₁) (A₁ := A₁) (R₁' := R₁') K
  let φ₁ := extendScalarsBaseChangeHom (A₁ := A₁) (A₁' := A₁') K K' φ
  let η := (totalDerivedExtensionScalarsAdjunction (algebraMap A' A₁')).unit
  let ρ := restrictSquareDerivedIso.{u, u, u, u, u} (algebraMap R' A') (algebraMap R' R₁')
    (algebraMap A' A₁') (algebraMap R₁' A₁') squareR'A₁'
  let β := (totalDerivedExtensionScalarsCompOfEq (algebraMap A A') (algebraMap A' A₁')
        (algebraMap A A₁') (IsScalarTower.algebraMap_eq A A' A₁').symm).hom.app K ≫
      (totalDerivedExtensionScalarsCompOfEq (algebraMap A A₁) (algebraMap A₁ A₁')
        (algebraMap A A₁') (IsScalarTower.algebraMap_eq A A₁ A₁').symm).inv.app K
  have hN : ψ ≫ rb.mapDerivedCategory.map τ₁ =
      τ₀ ≫ ri.mapDerivedCategory.map (η.app ((dext (algebraMap A A')).obj K)) ≫
        ρ.hom.app ((dext (algebraMap A' A₁')).obj ((dext (algebraMap A A')).obj K)) ≫
        rb.mapDerivedCategory.map (ri₁.mapDerivedCategory.map β) :=
    secondSquareDerivedMap_comp K
  have hβ : β ≫ φ₁ = (dext (algebraMap A' A₁')).map φ :=
    (Category.assoc _ _ _).trans
      (compOfEq_comp_extendScalarsBaseChangeHom (A₁ := A₁) (A₁' := A₁') K K' φ)
  have hρ : ρ.hom.app ((dext (algebraMap A' A₁')).obj ((dext (algebraMap A A')).obj K)) ≫
      rb.mapDerivedCategory.map (ri₁.mapDerivedCategory.map ((dext (algebraMap A' A₁')).map φ)) =
      ri.mapDerivedCategory.map (rs.mapDerivedCategory.map ((dext (algebraMap A' A₁')).map φ)) ≫
        ρ.hom.app K₁' :=
    (ρ.hom.naturality ((dext (algebraMap A' A₁')).map φ)).symm
  have hη : η.app ((dext (algebraMap A A')).obj K) ≫
      rs.mapDerivedCategory.map ((dext (algebraMap A' A₁')).map φ) = φ ≫ η.app K' :=
    (η.naturality φ).symm
  -- the derived equation
  have hD : ψ ≫ rb.mapDerivedCategory.map (τ₁ ≫ ri₁.mapDerivedCategory.map φ₁) =
      τ₀ ≫ ri.mapDerivedCategory.map φ ≫ ri.mapDerivedCategory.map (η.app K') ≫ ρ.hom.app K₁' := by
    rw [CategoryTheory.Functor.map_comp, reassoc_of% hN, ← CategoryTheory.Functor.map_comp,
      ← CategoryTheory.Functor.map_comp, hβ, hρ, ← ri.mapDerivedCategory.map_comp_assoc,
      hη, ri.mapDerivedCategory.map_comp, Category.assoc]
  have hCH := homology_restrictSquareDerivedIso (algebraMap R' A') (algebraMap R' R₁')
    (algebraMap A' A₁') (algebraMap R₁' A₁') squareR'A₁' K₁' n
  have hιb := ιb.naturality (τ₁ ≫ ri₁.mapDerivedCategory.map φ₁)
  have hιi := ιi.naturality (η.app K')
  -- the equation of morphisms
  have hM : (HR'.map ψ ≫ ιb.app _) ≫ rb.map (HR₁'.map (τ₁ ≫ ri₁.mapDerivedCategory.map φ₁) ≫
      ιi₁.app K₁') =
      (HR'.map (τ₀ ≫ ri.mapDerivedCategory.map φ) ≫ ιi.app K') ≫
        ri.map (HA'.map (η.app K') ≫ ιs.app K₁') ≫
        (restrictSquareIso.{u, u, u, u, u} (algebraMap R' A') (algebraMap R' R₁')
          (algebraMap A' A₁') (algebraMap R₁' A₁') squareR'A₁').hom.app (HA₁'.obj K₁') := by
    simp only [Functor.comp_map] at hιb hιi
    rw [Category.assoc, rb.map_comp, ← reassoc_of% hιb, ← HR'.map_comp_assoc, hD]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [hCH, reassoc_of% hιi]
  exact congrArg (fun t => t.hom m) hM

end SecondSquare

end RingTheory.TorIndependence

end
