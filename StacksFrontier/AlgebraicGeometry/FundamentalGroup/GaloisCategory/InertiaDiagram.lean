module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.MorphismMap
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.StrictlyHenselianSplitting
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import StacksFrontier.RingTheory.Henselian.FiniteEtale
public import StacksCore.Tactic.StacksAttribute

/-!
# The inertia diagram of fundamental groups

Let `A` be a normal local domain with fraction field `K`, let `Ah` and `Ash` be its henselization
and a strict henselization, and let `Kh` and `Ksh` be the corresponding fraction fields. The
inclusions of rings induce five arrows between the étale fundamental groups of the spectra, and
they fit into the *inertia diagram*: the square

```
π₁(Spec Ksh) → π₁(Spec Kh) → π₁(Spec K)
                  ↓              ↓
              π₁(Spec Ah) →  π₁(Spec A)
```

commutes, and the diagonal `π₁(Spec Ksh) → π₁(Spec Ah)` is trivial.

Both statements come from functoriality of `AlgebraicGeometry.etaleFundamentalGroupMap` under
composition, together with one geometric input: a strictly henselian local ring has trivial
étale fundamental group, because every finite étale cover of its spectrum splits as a finite
disjoint union of copies of the base, so each point of a geometric fibre extends to a section
and the fibre functor admits no nontrivial automorphism.

## Main definitions

* `AlgebraicGeometry.finiteEtaleOverTerminal` — the base itself, as the terminal finite étale
  cover.

## Main results

* `AlgebraicGeometry.etaleFundamentalGroupMap_comp` — the map induced by a composite is the
  composite of the induced maps.
* `AlgebraicGeometry.subsingleton_etaleFundamentalGroup_of_isSepClosed_residueField` — a
  strictly henselian local spectrum has trivial étale fundamental group.
* `AlgebraicGeometry.etaleFundamentalGroupMap_inertiaSquare` — the right-hand square of the
  inertia diagram commutes.
* `AlgebraicGeometry.etaleFundamentalGroupMap_fractionField_strictHenselization_to_henselization`
  — the diagonal of the inertia diagram is trivial.
* `AlgebraicGeometry.finiteEtale_algEquiv_pi_of_henselian_isSepClosed` and
  `AlgebraicGeometry.finiteEtaleOver_spec_iso_pi_of_henselian_isSepClosed` — the splitting of a
  finite étale algebra, respectively of a finite étale cover, over a strictly henselian local
  ring.
* `AlgebraicGeometry.isAffine_left_of_finiteEtaleOver_spec` — a scheme finite étale over an
  affine scheme is affine.

## Implementation notes

The two tagged statements are heterogeneous equalities, respectively an equality of continuous
homomorphisms whose codomain is indexed by a geometric point: the geometric point of
`Spec A` induced along the two sides of the square is the *same* point only up to the
propositional equality `AlgebraicGeometry.GeometricPoint.map_map`, so `HEq` is what the square
literally asserts. `AlgebraicGeometry.etaleFundamentalGroupMap_comp` has the same shape for the
same reason.

The splitting of a finite étale cover of a strictly henselian local spectrum is obtained
algebraically: the cover is affine, its global sections are a finite étale `R`-algebra, and
`CommAlgCat.FiniteEtale.baseChange` to the residue field is fully faithful, so a splitting over
the separably closed residue field lifts. Choosing a component of the resulting disjoint union
uses that the source of a geometric point is connected.

The projections to the fibres of the original covers are
`AlgebraicGeometry.finiteEtaleFiberProjection` and its bijection
`AlgebraicGeometry.finiteEtaleFiberProjectionEquiv`.

## References

* [Stacks Project, Tag 0BSV](https://stacks.math.columbia.edu/tag/0BSV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A scheme finite étale over an affine scheme is affine. -/
theorem isAffine_left_of_finiteEtaleOver_spec
    (R : Type u) [CommRing R] (Y : FiniteEtaleOver (Spec (.of R))) : IsAffine Y.left := by
  let : IsFinite Y.hom := Y.prop.1
  let : IsAffineHom Y.hom := inferInstance
  let : IsAffine ((Functor.fromPUnit (Spec (CommRingCat.of R))).obj Y.right) := by
    change IsAffine (Spec (CommRingCat.of R))
    infer_instance
  exact isAffine_of_isAffineHom Y.hom

/-- A finite étale algebra over a henselian local ring with separably closed residue field is a
finite product of copies of the ring: the splitting over the residue field lifts, because base
change along the residue map is fully faithful on finite étale algebras. -/
@[ega "IV 18.3.3" "more general", ega "IV 18.8.1" "(a)⇒(b)"]
theorem finiteEtale_algEquiv_pi_of_henselian_isSepClosed
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S] [Algebra.Etale R S] :
    ∃ n : ℕ, Nonempty (S ≃ₐ[R] (Fin n → R)) := by
  classical
  let k := IsLocalRing.ResidueField R
  let B := CommAlgCat.FiniteEtale.of R S
  let F := CommAlgCat.FiniteEtale.baseChange R k
  let C := F.obj B
  let : Algebra.IsFiniteSplit k C.obj := inferInstance
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun k C.obj
  let D := CommAlgCat.FiniteEtale.of R (Fin n → R)
  let e' : TensorProduct R k (Fin n → R) ≃ₐ[k] (Fin n → k) :=
    (Algebra.TensorProduct.piRight R k k (fun _ : Fin n => R)).trans
      (AlgEquiv.piCongrRight fun _ => Algebra.TensorProduct.rid R k k)
  let φ : C ≅ F.obj D := CommAlgCat.FiniteEtale.isoMk (e.trans e'.symm)
  let : F.Full := by
    dsimp [F]
    infer_instance
  let : F.Faithful := by
    dsimp [F]
    infer_instance
  let hF : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  let ψ : B.obj ≅ D.obj := (CommAlgCat.finiteEtale R).ι.mapIso (hF.isoEquiv.symm φ)
  exact ⟨n, ⟨CommAlgCat.algEquivOfIso ψ⟩⟩

/-- The splitting of `AlgebraicGeometry.finiteEtale_algEquiv_pi_of_henselian_isSepClosed`, with the
index type lifted into the ambient universe. -/
theorem finiteEtale_algEquiv_pi_ulift_of_henselian_isSepClosed
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (S : Type u) [CommRing S] [Algebra R S] [Module.Finite R S] [Algebra.Etale R S] :
    ∃ n : ℕ, Nonempty (S ≃ₐ[R] (ULift.{u} (Fin n) → R)) := by
  obtain ⟨n, ⟨e⟩⟩ := finiteEtale_algEquiv_pi_of_henselian_isSepClosed R S
  exact ⟨n, ⟨e.trans (AlgEquiv.piCongrLeft' R (fun _ : Fin n => R) Equiv.ulift.symm)⟩⟩

/-- Every finite étale cover of the spectrum of a henselian local ring with separably closed
residue field is isomorphic, over the base, to a finite disjoint union of copies of the base. -/
@[ega "IV 18.3.3" "more general", ega "IV 18.8.1" "(a)⇒(b)"]
theorem finiteEtaleOver_spec_iso_pi_of_henselian_isSepClosed
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] (Y : FiniteEtaleOver (Spec (.of R))) :
    ∃ n : ℕ, ∃ e : Y.left ≅ Spec (.of (ULift.{u} (Fin n) → R)),
      e.hom ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R (ULift.{u} (Fin n) → R))) = Y.hom := by
  let : IsAffine Y.left := isAffine_left_of_finiteEtaleOver_spec R Y
  let : IsFinite Y.hom := Y.prop.1
  let : Etale Y.hom := Y.prop.2
  let φ : CommRingCat.of R ⟶ CommRingCat.of Γ(Y.left, ⊤) :=
    Spec.preimage (Y.left.isoSpec.inv ≫ Y.hom)
  let : Algebra R Γ(Y.left, ⊤) := φ.hom.toAlgebra
  have hfin : Module.Finite R Γ(Y.left, ⊤) := by
    rw [← RingHom.finite_algebraMap]
    apply (IsFinite.SpecMap_iff φ).mp
    rw [Spec.map_preimage]
    infer_instance
  have heta : Algebra.Etale R Γ(Y.left, ⊤) := by
    rw [← RingHom.etale_algebraMap]
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    rw [Spec.map_preimage]
    infer_instance
  let := hfin
  let := heta
  obtain ⟨n, ⟨e⟩⟩ := finiteEtale_algEquiv_pi_ulift_of_henselian_isSepClosed R Γ(Y.left, ⊤)
  let i : CommRingCat.of Γ(Y.left, ⊤) ≅ CommRingCat.of (ULift.{u} (Fin n) → R) :=
    e.toRingEquiv.toCommRingCatIso
  let f := Spec.map i.hom
  let : IsIso f := inferInstance
  let ξ := Y.left.isoSpec ≪≫ (asIso f).symm
  refine ⟨n, ξ, ?_⟩
  apply (cancel_epi Y.left.isoSpec.inv).mp
  dsimp [ξ]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hf : inv f = Spec.map i.inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    change Spec.map i.hom ≫ Spec.map i.inv = 𝟙 _
    rw [← Spec.map_comp]
    simp
  rw [hf, ← Spec.map_comp, ← Spec.map_preimage (Y.left.isoSpec.inv ≫ Y.hom)]
  refine Spec.map_inj.mpr (CommRingCat.hom_ext ?_)
  ext r
  exact e.symm.commutes r

/-- Base change of finite étale covers along a composite is the composite of the base changes. -/
private noncomputable def finiteEtaleBaseChangeCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    finiteEtaleBaseChange (f ≫ g) ≅ finiteEtaleBaseChange g ⋙ finiteEtaleBaseChange f :=
  MorphismProperty.Over.pullbackComp (P := finiteEtale) (Q := ⊤) f g

/-- An automorphism of the fibre functor commutes with the maps induced by morphisms of covers. -/
private theorem fiberFunctor_map_apply_app {X : Scheme.{u}} [ConnectedSpace X]
    {x : GeometricPoint X} (σ : EtaleFundamentalGroup X x) {U V : FiniteEtaleOver X} (m : U ⟶ V)
    (q : finiteEtaleFiber x U) :
    (finiteEtaleFiberFunctor x).map m ((σ.asIso.app U).hom q) =
      (σ.asIso.app V).hom ((finiteEtaleFiberFunctor x).map m q) :=
  (congrArg (fun k => k q) (σ.asIso.hom.naturality m)).symm

/-- The fibre projections of Stacks 0BQA are compatible with composition, once a point of the
fibre over the composite is transported through `finiteEtaleBaseChangeCompIso`. -/
private theorem finiteEtaleFiberProjection_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : GeometricPoint X) (V : FiniteEtaleOver Z)
    (p : finiteEtaleFiber x ((finiteEtaleBaseChange (f ≫ g)).obj V)) :
    finiteEtaleFiberProjection g (x.map f) V
        (finiteEtaleFiberProjection f x ((finiteEtaleBaseChange g).obj V)
          ((finiteEtaleFiberFunctor x).map ((finiteEtaleBaseChangeCompIso f g).hom.app V) p)) =
      finiteEtaleFiberProjection (f ≫ g) x V p := by
  refine Subtype.ext ?_
  have hp' : ((finiteEtaleBaseChangeCompIso f g).hom.app V).left ≫
      pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g =
      pullback.fst V.hom (f ≫ g) :=
    MorphismProperty.Over.pullbackComp_left_fst_fst (P := finiteEtale) (Q := ⊤) f g V
  calc (p.1 ≫ ((finiteEtaleBaseChangeCompIso f g).hom.app V).left) ≫
        pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g
      = p.1 ≫ (((finiteEtaleBaseChangeCompIso f g).hom.app V).left ≫
          pullback.fst (pullback.snd V.hom g) f ≫ pullback.fst V.hom g) :=
        Category.assoc _ _ _
    _ = p.1 ≫ pullback.fst V.hom (f ≫ g) := congrArg (p.1 ≫ ·) hp'

/-- Composing a geometric point with a composite of morphisms is composing it twice. -/
theorem GeometricPoint.map_map {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : GeometricPoint X) : (x.map f).map g = x.map (f ≫ g) := by
  cases x
  simp [GeometricPoint.map, Category.assoc]

/-- **Stacks Project, Tag 0BND.** The map on étale fundamental groups induced by a composite is
the composite of the induced maps. The heterogeneous equality accounts for the two
propositionally equal induced geometric points of the target, compared by
`AlgebraicGeometry.GeometricPoint.map_map`. -/
theorem etaleFundamentalGroupMap_comp {X Y Z : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    [ConnectedSpace Z] (f : X ⟶ Y) (g : Y ⟶ Z) (x : GeometricPoint X)
    (σ : EtaleFundamentalGroup X x) :
    HEq (etaleFundamentalGroupMap g (x.map f) (etaleFundamentalGroupMap f x σ))
      (etaleFundamentalGroupMap (f ≫ g) x σ) := by
  cases GeometricPoint.map_map f g x
  refine heq_of_eq (CategoryTheory.Aut.ext ?_)
  let BCf := finiteEtaleBaseChange f
  let BCg := finiteEtaleBaseChange g
  let BCfg := finiteEtaleBaseChange (f ≫ g)
  let e := finiteEtaleBaseChangeCompIso f g
  let α := etaleFundamentalGroupMap f x σ
  let β := etaleFundamentalGroupMap g (x.map f) α
  let δ := etaleFundamentalGroupMap (f ≫ g) x σ
  ext V p
  let p₀ := (finiteEtaleFiberProjectionEquiv (f ≫ g) x V).symm p
  let p₁ := (finiteEtaleFiberFunctor x).map (e.hom.app V) p₀
  let p₂ := finiteEtaleFiberProjection f x (BCg.obj V) p₁
  have hnat : (finiteEtaleFiberFunctor x).map (e.hom.app V) (((σ.asIso.app (BCfg.obj V)).hom) p₀) =
      (σ.asIso.app ((BCg ⋙ BCf).obj V)).hom p₁ :=
    fiberFunctor_map_apply_app σ (e.hom.app V) p₀
  have hf := etaleFundamentalGroupMap_finiteEtaleFiberProjection f x (BCg.obj V) σ p₁
  have hg := etaleFundamentalGroupMap_finiteEtaleFiberProjection g (x.map f) V α p₂
  have hpc := finiteEtaleFiberProjection_comp f g x V (((σ.asIso.app (BCfg.obj V)).hom) p₀)
  rw [hnat] at hpc
  have hcomp := etaleFundamentalGroupMap_finiteEtaleFiberProjection (f ≫ g) x V σ p₀
  have hβ : (β.asIso.app V).hom p =
      finiteEtaleFiberProjection g (x.map f) V
        (finiteEtaleFiberProjection f x (BCg.obj V)
          (((σ.asIso.app ((BCg ⋙ BCf).obj V)).hom) p₁)) := by
    calc (β.asIso.app V).hom p
        = (β.asIso.app V).hom (finiteEtaleFiberProjection g (x.map f) V p₂) := by
          congr 1
          exact ((finiteEtaleFiberProjectionEquiv (f ≫ g) x V).apply_symm_apply p).symm.trans
            (finiteEtaleFiberProjection_comp f g x V p₀).symm
      _ = finiteEtaleFiberProjection g (x.map f) V ((α.asIso.app (BCg.obj V)).hom p₂) := hg.symm
      _ = finiteEtaleFiberProjection g (x.map f) V
            (finiteEtaleFiberProjection f x (BCg.obj V)
              (((σ.asIso.app ((BCg ⋙ BCf).obj V)).hom) p₁)) := by
          congr 1
          exact hf.symm
  have hδ : finiteEtaleFiberProjection (f ≫ g) x V (((σ.asIso.app (BCfg.obj V)).hom) p₀) =
      (δ.asIso.app V).hom p := by
    rw [hcomp]
    congr 1
    exact (finiteEtaleFiberProjectionEquiv (f ≫ g) x V).apply_symm_apply p
  exact hβ.trans (hpc.trans hδ)

/-- A morphism from a connected scheme into a coproduct of schemes factors through one
summand. -/
private theorem factor_through_sigma_of_connected {ι : Type u} [TopologicalSpace ι]
    [DiscreteTopology ι] [Small.{u} ι] (g : ι → Scheme.{u}) (X : Scheme.{u}) [ConnectedSpace X]
    (f : X ⟶ ∐ g) :
    ∃ i, ∃ t : X ⟶ g i, t ≫ Sigma.ι g i = f := by
  let q : X → ι := fun x => ((sigmaMk g).symm (f x)).1
  have hfst : Continuous (fun p : (Σ i, g i) => p.1) := continuous_sigma fun _ => continuous_const
  have hq : Continuous q := hfst.comp ((sigmaMk g).symm.continuous.comp f.continuous)
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  let i := q x
  have hrange : Set.range f ⊆ Set.range (Sigma.ι g i) := by
    rintro y ⟨z, rfl⟩
    cases h : (sigmaMk g).symm (f z) with
    | mk j w =>
      have hj : j = i := by
        rw [← show q z = j by simp [q, h]]
        exact PreconnectedSpace.constant (inferInstance : PreconnectedSpace X) hq
      have hzw : (sigmaMk g) ⟨j, w⟩ = f z := by
        simpa [h] using (sigmaMk g).apply_symm_apply (f z)
      subst j
      exact ⟨w, by simpa [sigmaMk_mk] using hzw⟩
  exact ⟨i, IsOpenImmersion.lift (Sigma.ι g i) f hrange,
    IsOpenImmersion.lift_fac (Sigma.ι g i) f hrange⟩

/-- The spectrum of a local ring is connected: its only idempotents are `0` and `1`. -/
theorem connectedSpace_spec_of_isLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    ConnectedSpace (Spec (.of R)) := by
  change ConnectedSpace (PrimeSpectrum R)
  refine connectedSpace_iff_clopen.mpr ⟨inferInstance, fun s hs => ?_⟩
  obtain ⟨e, he, h⟩ := PrimeSpectrum.isClopen_iff.mp hs
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · have heq : e = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp he
    right
    rw [h, heq]
    simp
  · have heq : 1 - e = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp he.one_sub
    left
    have he0 : e = 0 := by simpa using sub_eq_iff_eq_add'.mp heq
    rw [h, he0]
    simp

/-- The spectrum maps of a tower of algebras compose accordingly. -/
private theorem spec_map_algebraMap_comp (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C)) := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (IsScalarTower.algebraMap_eq A B C).symm)

/-- A section of a split finite étale cover over a connected open subscheme extends to a section
over the whole base: the section lands in a single summand, and that summand is the base. -/
private alias extend_section_to_split_finiteEtale := exists_section_of_split

/-- The base itself, as the terminal finite étale cover. -/
def finiteEtaleOverTerminal (X : Scheme.{u}) : FiniteEtaleOver X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) ⟨by infer_instance, by infer_instance⟩

/-- **Stacks Project, Tag 0BSV.** A strictly henselian local spectrum has trivial étale
fundamental group: every finite étale cover splits, so every point of a geometric fibre is the
image of the canonical point of the terminal cover under a morphism of covers, and a natural
automorphism of the fibre functor is determined by its value there. -/
theorem subsingleton_etaleFundamentalGroup_of_isSepClosed_residueField (R : Type u) [CommRing R]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    [ConnectedSpace (Spec (.of R))] (x : GeometricPoint (Spec (.of R))) :
    Subsingleton (EtaleFundamentalGroup (Spec (.of R)) x) := by
  classical
  let : ConnectedSpace x.source := by
    change ConnectedSpace (PrimeSpectrum x.residueField)
    infer_instance
  refine ⟨fun σ τ => CategoryTheory.Aut.ext ?_⟩
  ext Y p
  obtain ⟨n, e, he⟩ := finiteEtaleOver_spec_iso_pi_of_henselian_isSepClosed R Y
  let pbase := Spec.map (CommRingCat.ofHom (algebraMap R (ULift.{u} (Fin n) → R)))
  have hpbase : (p.1 ≫ e.hom) ≫ pbase = x.hom := by
    calc (p.1 ≫ e.hom) ≫ pbase = p.1 ≫ (e.hom ≫ pbase) := Category.assoc _ _ _
      _ = p.1 ≫ Y.hom := by rw [he]
      _ = x.hom := p.2
  obtain ⟨t, ht, hpt⟩ :=
    extend_section_to_split_finiteEtale R n x.source x.hom (p.1 ≫ e.hom) hpbase
  let sec := t ≫ e.inv
  have hsec : sec ≫ Y.hom = 𝟙 (Spec (.of R)) := by
    calc sec ≫ Y.hom = t ≫ (e.inv ≫ Y.hom) := by simp [sec, Category.assoc]
      _ = t ≫ pbase := by rw [← he, Iso.inv_hom_id_assoc]
      _ = 𝟙 _ := ht
  have hfactor : x.hom ≫ sec = p.1 := by
    calc x.hom ≫ sec = (x.hom ≫ t) ≫ e.inv := by simp [sec, Category.assoc]
      _ = (p.1 ≫ e.hom) ≫ e.inv := by rw [hpt]
      _ = p.1 := by simp [Category.assoc]
  let T := finiteEtaleOverTerminal (Spec (.of R))
  let q : finiteEtaleFiber x T := ⟨x.hom, by
    change x.hom ≫ 𝟙 _ = x.hom
    exact Category.comp_id _⟩
  have hT : (σ.asIso.app T).hom q = (τ.asIso.app T).hom q := by
    refine Subtype.ext ?_
    have hs : ((σ.asIso.app T).hom q).1 ≫ 𝟙 _ = x.hom := ((σ.asIso.app T).hom q).property
    have ht : ((τ.asIso.app T).hom q).1 ≫ 𝟙 _ = x.hom := ((τ.asIso.app T).hom q).property
    simpa using hs.trans ht.symm
  let m : T ⟶ Y := MorphismProperty.Over.homMk sec hsec
  have hmap : (finiteEtaleFiberFunctor x).map m q = p := Subtype.ext hfactor
  have hσ := fiberFunctor_map_apply_app σ m q
  have hτ := fiberFunctor_map_apply_app τ m q
  rw [hmap] at hσ hτ
  exact hσ.symm.trans (hT ▸ hτ)

/-- **Stacks Project, Tag 0BSV.** The square formed by the generic and local spectra of a ring
extension commutes on fundamental groups. In the inertia diagram the extension is `A → Ah`, with
fraction fields `K → Kh`. The heterogeneous equality accounts for the two propositionally equal
induced geometric points of `Spec A`. -/
@[stacks 0BSV "right-hand square"]
theorem etaleFundamentalGroupMap_inertiaSquare
    (A Ah K Kh : Type u)
    [CommRing A] [CommRing Ah] [Algebra A Ah]
    [Field K] [Algebra A K]
    [Field Kh] [Algebra Ah Kh] [Algebra K Kh] [Algebra A Kh]
    [IsScalarTower A Ah Kh] [IsScalarTower A K Kh]
    [ConnectedSpace (Spec (.of Ah))] [ConnectedSpace (Spec (.of A))]
    [ConnectedSpace (Spec (.of Kh))] [ConnectedSpace (Spec (.of K))]
    (x : GeometricPoint (Spec (.of Kh)))
    (σ : EtaleFundamentalGroup (Spec (.of Kh)) x) :
    HEq
      (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (algebraMap A K)))
        (x.map (Spec.map (CommRingCat.ofHom (algebraMap K Kh))))
        (etaleFundamentalGroupMap
          (Spec.map (CommRingCat.ofHom (algebraMap K Kh))) x σ))
      (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (algebraMap A Ah)))
        (x.map (Spec.map (CommRingCat.ofHom (algebraMap Ah Kh))))
        (etaleFundamentalGroupMap
          (Spec.map (CommRingCat.ofHom (algebraMap Ah Kh))) x σ)) := by
  let f₁ := Spec.map (CommRingCat.ofHom (algebraMap K Kh))
  let g₁ := Spec.map (CommRingCat.ofHom (algebraMap A K))
  let f₂ := Spec.map (CommRingCat.ofHom (algebraMap Ah Kh))
  let g₂ := Spec.map (CommRingCat.ofHom (algebraMap A Ah))
  have hcomp : f₁ ≫ g₁ = f₂ ≫ g₂ :=
    (spec_map_algebraMap_comp A K Kh).trans (spec_map_algebraMap_comp A Ah Kh).symm
  have hmid : HEq (etaleFundamentalGroupMap (f₁ ≫ g₁) x σ)
      (etaleFundamentalGroupMap (f₂ ≫ g₂) x σ) := by rw [hcomp]
  exact (etaleFundamentalGroupMap_comp f₁ g₁ x σ).trans
    (hmid.trans (etaleFundamentalGroupMap_comp f₂ g₂ x σ).symm)

/-- **Stacks Project, Tag 0BSV.** The diagonal of the inertia diagram is the trivial map: it
factors through the fundamental group of the strictly henselian spectrum of `Ash`, which is
trivial. -/
@[stacks 0BSV "trivial diagonal"]
theorem etaleFundamentalGroupMap_fractionField_strictHenselization_to_henselization
    (A Ah Ash Ksh κsep : Type u)
    [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) Ah]
    [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash] [Algebra Ah Ash]
    [IsScalarTower A Ah Ash]
    [Field κsep] [Algebra (IsLocalRing.ResidueField A) κsep]
    [IsSepClosure (IsLocalRing.ResidueField A) κsep]
    [IsLocalRing.IsHenselization A κsep Ash]
    [Field Ksh] [Algebra Ash Ksh] [Algebra A Ksh] [IsFractionRing Ash Ksh]
    [Algebra Ah Ksh]
    [IsScalarTower Ah Ash Ksh] [IsScalarTower A Ash Ksh]
    [ConnectedSpace (Spec (.of Ksh))] [ConnectedSpace (Spec (.of Ah))]
    (x : GeometricPoint (Spec (.of Ksh))) :
    etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap Ah Ksh))) x = 1 := by
  let : HenselianLocalRing Ash :=
    (inferInstance : IsLocalRing.IsHenselization A κsep Ash).henselian
  let : IsSepClosed κsep := IsSepClosure.sep_closed (IsLocalRing.ResidueField A)
  obtain ⟨eκ⟩ :=
    IsLocalRing.IsHenselization.exists_residueFieldEquiv (R := A) (L := κsep) (Rh := Ash)
  let : IsSepClosed (IsLocalRing.ResidueField Ash) := IsSepClosed.of_ringEquiv eκ.symm
  let : ConnectedSpace (Spec (.of Ash)) := connectedSpace_spec_of_isLocalRing Ash
  let f : Spec (.of Ksh) ⟶ Spec (.of Ash) :=
    Spec.map (CommRingCat.ofHom (algebraMap Ash Ksh))
  let g : Spec (.of Ash) ⟶ Spec (.of Ah) := Spec.map (CommRingCat.ofHom (algebraMap Ah Ash))
  have hfg : f ≫ g = Spec.map (CommRingCat.ofHom (algebraMap Ah Ksh)) :=
    spec_map_algebraMap_comp Ah Ash Ksh
  let y := x.map f
  let : Subsingleton (EtaleFundamentalGroup (Spec (.of Ash)) y) :=
    subsingleton_etaleFundamentalGroup_of_isSepClosed_residueField Ash y
  ext σ
  have hcomp := etaleFundamentalGroupMap_comp f g x σ
  have h₁ : etaleFundamentalGroupMap f x σ = 1 := Subsingleton.elim _ _
  have hleft : etaleFundamentalGroupMap g y (etaleFundamentalGroupMap f x σ) =
      (1 : EtaleFundamentalGroup (Spec (.of Ksh)) x →ₜ*
        EtaleFundamentalGroup (Spec (.of Ah)) ((x.map f).map g)) σ := by
    rw [h₁]
    simp
  have hmid : HEq (etaleFundamentalGroupMap (f ≫ g) x σ)
      (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap Ah Ksh))) x σ) := by
    rw [hfg]
  have hpoint : (x.map f).map g = x.map (Spec.map (CommRingCat.ofHom (algebraMap Ah Ksh))) := by
    calc (x.map f).map g = x.map (f ≫ g) := GeometricPoint.map_map f g x
      _ = x.map (Spec.map (CommRingCat.ofHom (algebraMap Ah Ksh))) :=
        congrArg (fun k => x.map k) hfg
  have hunit : HEq
      ((1 : EtaleFundamentalGroup (Spec (.of Ksh)) x →ₜ*
        EtaleFundamentalGroup (Spec (.of Ah)) ((x.map f).map g)) σ)
      ((1 : EtaleFundamentalGroup (Spec (.of Ksh)) x →ₜ*
        EtaleFundamentalGroup (Spec (.of Ah))
          (x.map (Spec.map (CommRingCat.ofHom (algebraMap Ah Ksh))))) σ) := hpoint ▸ HEq.rfl
  exact eq_of_heq ((hcomp.trans hmid).symm.trans ((heq_of_eq hleft).trans hunit))

end AlgebraicGeometry

end
