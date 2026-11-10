module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GeometricPointStalkMap

/-!
# The endomorphism of a strict henselization induced by an endomorphism of the geometric point

Let `s̄` be a geometric point of a scheme `S` and `a : s̄ ⟶ s̄` an endomorphism over `S` (for a
geometric point over a closed point with finite residue field, a lift of Frobenius). The map of
Tag 04FN along `a` on the stalk of the structure sheaf is a ring endomorphism `θ_a` of the étale
local ring `𝒪^{sh}_{S,s̄}`: it sends the germ at an étale neighbourhood `(V, v̄)` to the germ at
`(V, v̄ ∘ a)`. Its spectrum `β_a` is an endomorphism of the strict henselization `Spec 𝒪^{sh}`
over `S` which is compatible with `a` on the canonical lift of the geometric point:

* `θ_a` fixes the image of the ordinary local ring `𝒪_{S,s}` (a Zariski neighbourhood has a
  unique lift of the geometric point), so `β_a ≫ (Spec 𝒪^{sh} → S) = (Spec 𝒪^{sh} → S)`;
* evaluating `θ_a(f)` in the residue field of `s̄` is `a` applied to the evaluation of `f`, so
  `(s̄ → Spec 𝒪^{sh}) ≫ β_a = a ≫ (s̄ → Spec 𝒪^{sh})`.

This is the action of the decomposition group on the strict henselization through which the
Frobenius acts on the stalk at a boundary point of a direct image `j_* F` (Weil II 1.8, the
Frobenius on `H⁰_loc`).

## Main definitions

* `AlgebraicGeometry.etaleLocalRingEndomorphism` — `θ_a`.
* `AlgebraicGeometry.strictHenselizationEndomorphism` — `β_a = Spec θ_a`.

## Main results

* `AlgebraicGeometry.etaleLocalRingEndomorphism_comp_structureSheafStalkFromLocalRing`,
  `AlgebraicGeometry.strictHenselizationEndomorphism_comp_toBase` — compatibility with `S`.
* `AlgebraicGeometry.structureSheafStalkToGeometricField_comp_etaleLocalRingEndomorphism`,
  `AlgebraicGeometry.geometricPointToStrictHenselization_comp_strictHenselizationEndomorphism` —
  compatibility with `a` on the geometric point.

## References

* [Stacks Project, Tag 04FN](https://stacks.math.columbia.edu/tag/04FN)
* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) (Weil II 1.8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {s : GeometricPoint S}
  (a : GeometricPoint.Hom s s)

/-- **The ring endomorphism of the étale local ring induced by an endomorphism `a` of the
geometric point**: the map of Tag 04FN along `a` on the stalk of the structure sheaf, sending the
germ at `(V, v̄)` to the germ at `(V, v̄ ∘ a)`. -/
def etaleLocalRingEndomorphism : etaleLocalRing B S hS s ⟶ etaleLocalRing B S hS s :=
  (geometricPointStalkMap B S hS a RingCat.{u}).app (SmallEtale.structureSheaf B S hS).obj

/-- `θ_a` on germs: the germ at `(V, v̄)` goes to the germ at `(V, v̄ ∘ a)`. -/
theorem etaleLocalRingEndomorphism_ι (U : (geometricPointFiber B S hS s).Elementsᵒᵖ) :
    colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj) U ≫ etaleLocalRingEndomorphism B S hS a =
      colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj) ((neighborhoodFunctor B S hS a).op.obj U) :=
  colimit.ι_pre ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
    (SmallEtale.structureSheaf B S hS).obj) (neighborhoodFunctor B S hS a).op U

/-- **Evaluating `θ_a(f)` at the geometric point is `a` applied to the evaluation of `f`.** -/
theorem structureSheafStalkToGeometricField_comp_etaleLocalRingEndomorphism :
    (structureSheafStalkToGeometricField B S hS s).comp
        (etaleLocalRingEndomorphism B S hS a).hom =
      (Spec.preimage a.hom).hom.comp (structureSheafStalkToGeometricField B S hS s) := by
  suffices h : etaleLocalRingEndomorphism B S hS a ≫
      RingCat.ofHom (structureSheafStalkToGeometricField B S hS s) =
      RingCat.ofHom (structureSheafStalkToGeometricField B S hS s) ≫
        RingCat.ofHom (Spec.preimage a.hom).hom from congrArg RingCat.Hom.hom h
  refine colimit.hom_ext fun U => ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ RingCat.ofHom (structureSheafStalkToGeometricField B S hS s))
    (etaleLocalRingEndomorphism_ι B S hS a U)).trans ?_
  ext f
  have h2 := RingHom.congr_fun (structureSheafStalkToGeometricField_ι B S hS s
    ((neighborhoodFunctor B S hS a).op.obj U)) f
  have h3 := RingHom.congr_fun (structureSheafStalkToGeometricField_ι B S hS s U) f
  refine h2.trans (Eq.trans ?_ (congrArg (fun z => (Spec.preimage a.hom).hom z) h3.symm))
  have key : a.hom.appTop ≫ (Scheme.ΓSpecIso (.of s.residueField)).hom =
      (Scheme.ΓSpecIso (.of s.residueField)).hom ≫ Spec.preimage a.hom := by
    conv_lhs => rw [← Spec.map_preimage a.hom]
    exact Scheme.ΓSpecIso_naturality _
  change (((a.hom ≫ U.unop.2.1).appTop ≫ (Scheme.ΓSpecIso (.of s.residueField)).hom).hom f) = _
  rw [Scheme.Hom.comp_appTop, Category.assoc, key]
  rfl

/-- Transport of a germ along an equality of points. -/
theorem germ_eqRec_eq {X : Scheme.{u}} (V : X.Opens) {y z : X} (e : y = z) (hz : z ∈ V)
    (b : Γ(X, V)) :
    (e ▸ X.presheaf.germ V y (e ▸ hz) b : X.presheaf.stalk z) = X.presheaf.germ V z hz b := by
  subst e
  rfl

/-- On a Zariski neighbourhood the lift of the geometric point is fixed by `a`: an open immersion
is a monomorphism. -/
theorem zariskiNeighborhood_point_eq (x : S) (hx : s.hom (closedPoint s.residueField) = x)
    (V : TopologicalSpace.OpenNhds x) :
    a.hom ≫ (zariskiNeighborhood B S hS s x hx V).2.1 =
      (zariskiNeighborhood B S hS s x hx V).2.1 := by
  refine (cancel_mono (Scheme.Opens.ι (X := S) V.1)).1 ?_
  have h := (zariskiNeighborhood B S hS s x hx V).2.2
  change (zariskiNeighborhood B S hS s x hx V).2.1 ≫ Scheme.Opens.ι (X := S) V.1 = s.hom at h
  exact (Category.assoc _ _ _).trans ((congrArg (a.hom ≫ ·) h).trans (a.comm.trans h.symm))

/-- **`θ_a` fixes the image of the ordinary local ring**: a germ of a function on a Zariski
neighbourhood is represented at an étale neighbourhood whose lift of the geometric point is
fixed by `a`. -/
theorem etaleLocalRingEndomorphism_comp_structureSheafStalkFromLocalRing :
    (etaleLocalRingEndomorphism B S hS a).hom.comp (structureSheafStalkFromLocalRing B S hS s) =
      structureSheafStalkFromLocalRing B S hS s := by
  refine RingHom.ext fun r => ?_
  obtain ⟨V, hV, b, rfl⟩ := S.presheaf.exists_germ_eq r
  let Z := zariskiNeighborhood B S hS s (s.hom (closedPoint s.residueField)) rfl ⟨V, hV⟩
  let f : (SmallEtale.toScheme B S hS).obj Z.1 ⟶ S := B.inclusion.map Z.1.obj.hom
  let y := Z.2.1 (closedPoint s.residueField)
  have hy : f y = s.hom (closedPoint s.residueField) :=
    (Scheme.Hom.comp_apply Z.2.1 f _).symm.trans
      (congrArg (fun q : s.source ⟶ S => q (closedPoint s.residueField)) Z.2.2)
  have hfy : f y ∈ V := hy.symm ▸ hV
  have htop : (⊤ : ((SmallEtale.toScheme B S hS).obj Z.1).Opens) ≤ f ⁻¹ᵁ V := by
    intro w _
    change (Scheme.Opens.ι (X := S) V).base w ∈ V
    exact (w : V).2
  let c : Γ((SmallEtale.toScheme B S hS).obj Z.1, ⊤) :=
    ((SmallEtale.toScheme B S hS).obj Z.1).presheaf.map (homOfLE htop).op (f.app V b)
  have hc : structureSheafStalkFromLocalRing B S hS s
      (S.presheaf.germ V (s.hom (closedPoint s.residueField)) hV b) =
      (colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
        (SmallEtale.structureSheaf B S hS).obj) (op Z)).hom c := by
    refine structureSheafStalkFromLocalRing_germ B S hS s (op Z) _ c ?_
    change (f.stalkMap y).hom (hy.symm ▸ S.presheaf.germ V _ hV b) = _
    rw [show (hy.symm ▸ S.presheaf.germ V (s.hom (closedPoint s.residueField)) hV b :
        S.presheaf.stalk (f y)) = S.presheaf.germ V (f y) hfy b from
      germ_eqRec_eq V hy.symm hfy b, Scheme.Hom.germ_stalkMap_apply]
    exact (TopCat.Presheaf.germ_res_apply _ (homOfLE htop) y trivial (f.app V b)).symm
  -- the neighbourhood `(Z, a ≫ p)` maps to `(Z, p)` by the identity
  let φ : (neighborhoodFunctor B S hS a).obj Z ⟶ Z :=
    Functor.Elements.homMk (𝟙 Z.1) (by
      refine Subtype.ext ?_
      change 𝟙 _ ≫ (a.hom ≫ Z.2.1) ≫ 𝟙 _ = Z.2.1
      rw [Category.id_comp, Category.comp_id]
      exact zariskiNeighborhood_point_eq B S hS a _ rfl ⟨V, hV⟩)
  rw [RingHom.comp_apply, hc]
  have h1 := congrArg (fun g => g.hom c) (etaleLocalRingEndomorphism_ι B S hS a (op Z))
  have h2 := congrArg (fun g => g.hom c)
    (colimit.w ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
      (SmallEtale.structureSheaf B S hS).obj) φ.op)
  simp only [RingCat.hom_comp] at h1 h2
  refine h1.trans (Eq.trans ?_ h2)
  congr 1

/-- **The endomorphism of the strict henselization induced by an endomorphism `a` of the
geometric point**: the spectrum of `θ_a`. -/
def strictHenselizationEndomorphism :
    strictHenselization B S hS s ⟶ strictHenselization B S hS s :=
  Spec.map (CommRingCat.ofHom (etaleLocalRingEndomorphism B S hS a).hom)

/-- **The canonical lift of the geometric point to the strict henselization intertwines `a` with
`β_a`.** -/
theorem geometricPointToStrictHenselization_comp_strictHenselizationEndomorphism :
    geometricPointToStrictHenselization B S hS s ≫ strictHenselizationEndomorphism B S hS a =
      a.hom ≫ geometricPointToStrictHenselization B S hS s := by
  rw [geometricPointToStrictHenselization, strictHenselizationEndomorphism, ← Spec.map_comp]
  conv_rhs => rw [← Spec.map_preimage a.hom, ← Spec.map_comp]
  congr 1
  ext x
  exact RingHom.congr_fun
    (structureSheafStalkToGeometricField_comp_etaleLocalRingEndomorphism B S hS a) x

/-- **`β_a` is an endomorphism over `S`.** -/
theorem strictHenselizationEndomorphism_comp_toBase :
    strictHenselizationEndomorphism B S hS a ≫ strictHenselizationToBase B S hS s =
      strictHenselizationToBase B S hS s := by
  rw [strictHenselizationToBase, strictHenselizationEndomorphism, ← Category.assoc,
    ← Spec.map_comp]
  congr 2
  ext r
  exact RingHom.congr_fun
    (etaleLocalRingEndomorphism_comp_structureSheafStalkFromLocalRing B S hS a) r

end AlgebraicGeometry

end
