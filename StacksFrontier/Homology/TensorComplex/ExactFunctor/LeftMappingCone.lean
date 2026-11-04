module

public import StacksFrontier.Homology.TensorComplex.ExactFunctor.Descent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensoring on the left commutes with mapping cones

The cone-commutation isomorphism `Tot(G ⊗ C(φ)) ≅ C(Tot(id_G ⊗ φ))`, the resulting
isomorphisms of mapping-cone triangles at the cochain level and in `K(C)`, and the consequence
that `Tleft G` sends distinguished triangles to distinguished triangles.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
  CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [∀ (K₁ K₂ : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor C) (ComplexShape.up ℤ)]

/- **Triangle preservation (left version) — overview.**  Equipped with the comparison datum
`TleftCommShift G`, the functor `Tleft G` sends distinguished triangles of `K(C)` to
distinguished triangles.  This is the substantive content of `main_left`.

ARGUMENT (Stacks Tag 06Y8): every distinguished
triangle of `K(C)` is, up to isomorphism, the image `triangleh φ` of the standard mapping-cone
triangle of some morphism of complexes `φ : F₁ ⟶ F₂` (`HomotopyCategory.mappingCone_triangleh
_distinguished`).  By `Pretriangulated.isomorphic_distinguished` it therefore suffices to show
`(Tleft G).mapTriangle.obj (triangleh φ)` is distinguished.  The tensor–total functor commutes
with the formation of mapping cones up to a canonical natural isomorphism of complexes
  `Tot(G ⊗ C(φ)) ≅ C(Tot(id_G ⊗ φ))`
(Tag 0FNG sign conventions; the cone of `Tot(id_G ⊗ φ)` is built from the same biproduct
`G ⊗ F₂ ⊕ (G ⊗ F₁)[1]` as `Tot(G ⊗ C(φ))`, using `mapBifunctorShift₂Iso` to identify the
shifted summand).  This isomorphism is compatible with the three triangle maps, so it upgrades
to an isomorphism of triangles
  `(Tleft G).mapTriangle.obj (triangleh φ) ≅ triangleh (Tot(id_G ⊗ φ))`
in `K(C)` (the comparison datum `ξ = TleftCommShift G` enters exactly in matching the
connecting map `δ`, which lands in a shift).  The right-hand triangle is distinguished by
`HomotopyCategory.mappingCone_triangleh_distinguished`, hence so is the left by
`isomorphic_distinguished`.

DECOMPOSITION for the formal phase: (i) construct the cochain-level cone-commutation iso
`Tot(G ⊗ C(φ)) ≅ C(Tot(id_G ⊗ φ))` from `CochainComplex.mappingCone` API +
`HomologicalComplex.mapBifunctor` + `mapBifunctorShift₂Iso`; (ii) check it is a map of
triangles compatible with `inl`/`inr`/`δ` and the descended `ξ`; (iii) descend to `K(C)` and
finish with `isomorphic_distinguished`.  This is the genuine analytic kernel of Tag 06Y8 and is
NOT currently available off-the-shelf in Mathlib. -/
/- **Cone-commutation triangle iso (left version) — the analytic kernel (K(C)-level overview).**

For a morphism of cochain complexes `φ : K ⟶ L`, the image under `Tleft G` of the standard
mapping-cone triangle `triangleh φ` is isomorphic, in `K(C)`, to the standard mapping-cone
triangle of `(TleftCochain G).map φ = Tot(id_G ⊗ φ)`.

This packages the genuine analytic content of Stacks Tag 06Y8 (left version): the total–tensor
functor commutes with the mapping-cone construction up to a canonical natural isomorphism of
complexes
  `Tot(G ⊗ C(φ)) ≅ C(Tot(id_G ⊗ φ))`,
compatible with the three triangle maps and with the descended comparison datum
`ξ = TleftCommShift G`.

DECOMPOSITION:
  Step 2a (object iso, RIGOROUS): on degree `n`,
    `Tot(G ⊗ C(φ))^n = ⊕_{p+q=n} G^p ⊗ (K^{q+1} ⊕ L^q)`
    `≅ (⊕_{p+q'=n+1} G^p ⊗ K^{q'}) ⊕ (⊕_{p+q=n} G^p ⊗ L^q) = C(Tot(id_G ⊗ φ))^n`,
    canonically from additivity of `G^p ⊗ −` / biproducts (`ιMapBifunctor`, `mapBifunctorDesc`).
  Step 2b (the HARD SIGN NUCLEUS): determine the Koszul/shift sign `ε(p,q)` on the `K`-summand
    (conjecturally `(p)·1`-type sign, matching `mapBifunctorShift₂Iso`'s `(p·y).negOnePow` at the
    relevant bidegree; `+1` on the `L`-summand) so that this object iso is a CHAIN MAP; verify the
    four differential blocks (`G`-diff, inner-`K`-diff, inner-`L`-diff, `φ`-off-diagonal) commute
    simultaneously, against Mathlib's `mappingCone` sign convention
    (`CochainComplex.mappingCone.inl_v_d`, `d_fst_v`, `d_snd_v`, `inr_f_d`) and
    `CochainComplex.ι_mapBifunctorShift₂Iso_hom_f`.
  Step 3 (triangle-map compatibility): the iso intertwines `inr`/`fst`/`snd` and the connecting
    map `δ` of the two cones, the `δ`-compatibility using the descended `ξ = TleftCommShift G`
    (`Functor.commShiftIso (Tleft G) 1` ≈ `mapBifunctorShift₂Iso`).
  Step 4 (descent, RIGOROUS): push the cochain triangle iso through `HomotopyCategory.quotient`
    (recall `triangleh ψ = quotient.mapTriangle.obj (triangle ψ)` and
    `descendF_comp_quotient`) to obtain the K(C)-triangle iso asserted here.

Key API: `CochainComplex.mappingCone`, `.triangle`, `.triangleh`, `.inl/.inr/.fst/.snd`,
`.inl_v_d/.d_fst_v/.d_snd_v/.inr_f_d`, `HomologicalComplex.mapBifunctor`, `.ιMapBifunctor`,
`.mapBifunctorDesc`, `CochainComplex.mapBifunctorShift₂Iso`, `.ι_mapBifunctorShift₂Iso_hom_f`,
`descendF_comp_quotient`, `Functor.commShiftIso`. This is NOT off-the-shelf in Mathlib. -/
/- **Cochain-level cone-commutation triangle iso (the genuine analytic kernel / sign nucleus).**

Before descending to `K(C)`, the cone-commutation isomorphism lives already at the level of
cochain complexes: the image under the cochain functor `TleftCochain G = Tot(G ⊗ −)` of the
standard mapping-cone triangle `triangle φ` is isomorphic (as a triangle in `CochainComplex C ℤ`)
to the standard mapping-cone triangle of `(TleftCochain G).map φ = Tot(id_G ⊗ φ)`.

This is the analytic heart of Stacks Tag 06Y8 (left), and is NOT off-the-shelf in Mathlib
(`mapTriangleIso`/`mapTrianglehIso` apply only to *degreewise* `H.mapHomologicalComplex`
functors, whereas `Tot(G ⊗ −)` is a total-complex/bifunctor functor).

INTENDED CONSTRUCTION (`Triangle.isoMk`):
  obj₁/obj₂ components are `Iso.refl` (both are `Tot(G ⊗ K)`, resp. `Tot(G ⊗ L)`, definitionally
    — `(TleftCochain G).mapTriangle.obj (triangle φ)` has `obj₁ = (TleftCochain G).obj K`,
    `obj₂ = (TleftCochain G).obj L`, matching `triangle ((TleftCochain G).map φ)`);
  obj₃ component is the cochain cone-object iso
    `Θ : (TleftCochain G).obj (mappingCone φ) ≅ mappingCone ((TleftCochain G).map φ)`,
    built degreewise (via `homotopyCofiber.XIsoBiprod` + `mapBifunctorDesc` + the biproduct
    decomposition `G^p ⊗ (K^{q+1} ⊕ L^q) ≅ (G^p⊗K^{q+1}) ⊕ (G^p⊗L^q)`) with the SIGN
    `ε(p) = (p).negOnePow = (-1)^p` on the `K`-summand (matching
    `CochainComplex.ι_mapBifunctorShift₂Iso_hom_f`'s `(n₁*y).negOnePow` at `y = 1`) and `+1`
    on the `L`-summand; `Θ` must be verified to be a CHAIN MAP (4 differential blocks:
    `G`-diff, inner-`K`-diff via `d_fst_v`, inner-`L`-diff via `d_snd_v`, off-diagonal `φ` via
    `inl_v_d`/`inr_f_d`, against `mapBifunctor.d₁_eq/d₂_eq`).
  The three `Triangle.isoMk` commutativity squares encode: `mor₁` compat (`φ` vs `Tot(id⊗φ)`),
  `mor₂` compat (the `inr` inclusions — sign-free `L`-summand), `mor₃` compat (the connecting map
  `δ = (-fst).rightShift 1`, where the `K`-summand sign and `commShiftIso = mapBifunctorShift₂Iso`
  enter). -/
/- **The cone-object iso (obj₃ component / the sign nucleus).**

The total–tensor functor `Tot(G ⊗ −) = TleftCochain G` commutes with the mapping-cone object:
`Tot(G ⊗ C(φ)) ≅ C(Tot(id_G ⊗ φ))`. Built degreewise from the biproduct decomposition
`G^p ⊗ (K^{q+1} ⊕ L^q) ≅ (G^p⊗K^{q+1}) ⊕ (G^p⊗L^q)` (`homotopyCofiber.XIsoBiprod` +
`mapBifunctorDesc`), with the Koszul sign `ε(q) = (q).negOnePow = (-1)^q` on the K-summand and
`+1` on the L-summand, so that it is a chain map. This is the genuine analytic kernel; the closer
validated the connecting cochain `alphaPrime` (= `Θ.inv`'s K-component) via `Cochain.mk` +
`mapBifunctorDesc` with the `(q).negOnePow` sign, and the obj₁/obj₂ identifications by `rfl`.

CONSTRUCTION (per closer's validated decomposition):
  `Θ.hom = mappingCone.lift _ a b` from a degree-1 cochain `a` (built from `fst φ`) and a
    degree-0 cochain `b` (built from `snd φ`); `Θ.inv = mappingCone.desc _ alphaPrime β` from
    `alphaPrime` (degree-(-1), K-summand, sign `(q).negOnePow`) and `β = (TleftCochain G).map (inr
    φ)`.
  The two δ-cocycle conditions and the two `hom_inv`/`inv_hom` identities are the 4 differential
  blocks: G-diff (`d₁`), inner-K (`d_fst_v`), inner-L (`d_snd_v`), off-diagonal φ
  (`inl_v_d`/`inr_f_d`),
  all checked via `mapBifunctor.hom_ext` / `δ_v`. -/
/-- **Θ.hom** (the forward cone-commutation map, sign nucleus).

A morphism `Tot(G ⊗ C(φ)) ⟶ C(Tot(id_G ⊗ φ))`. By `mappingCone.lift` (the universal property of
the *codomain* cone `C(Tot(id_G ⊗ φ))`), it is determined by a degree-`1` cocycle
`a : Cocycle (Tot(G⊗C(φ))) (Tot(G⊗K)) 1` and a degree-`0` cochain
`b : Cochain (Tot(G⊗C(φ))) (Tot(G⊗L)) 0` satisfying the lift δ-cocycle condition
`δ 0 1 b + a.comp (ofHom ((TleftCochain G).map φ)) = 0`.

On the degree-`n` biproduct summands of `Tot(G⊗C(φ))^n`
(`⊕_{p+q=n} G^p⊗(K^{q+1}⊕L^q)`, via `homotopyCofiber.XIsoBiprod φ q (q+1) rfl` and
`ιMapBifunctor`), `a` extracts the `K`-summand `G^p⊗K^{q+1}` with the Koszul sign `ε(p)=(-1)^p`
(`(p).negOnePow`) into `Tot(G⊗K)`, and `b` extracts the `L`-summand `G^p⊗L^q` with sign `+1` into
`Tot(G⊗L)`. Concretely `a`/`b` are built from `mappingCone.fst φ`/`mappingCone.snd φ` precomposed
with the bifunctor-summand projections. The δ-cocycle condition is the chain-map condition of `Θ`,
verified blockwise via `mapBifunctor.hom_ext` (`d₁_eq`/`d₂_eq`) and the
cone differential lemmas `inl_v_d`/`inr_f_d`/`d_fst_v`/`d_snd_v`. -/
noncomputable def TleftCochain_mappingCone_hom (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    (TleftCochain G).obj (CochainComplex.mappingCone φ) ⟶
      CochainComplex.mappingCone ((TleftCochain G).map φ) := by
  -- Build via `CochainComplex.mappingCone.lift _ a b hab` with `a` (degree 1, K-summand, sign
  -- `(p).negOnePow`) from `fst φ`, `b` (degree 0, L-summand) from `snd φ`, and `hab` the lift
  -- δ-cocycle condition (= the K/L chain-map blocks).
  let aCoch : CochainComplex.HomComplex.Cochain
      ((TleftCochain G).obj (CochainComplex.mappingCone φ))
      ((TleftCochain G).obj K) 1 :=
    CochainComplex.HomComplex.Cochain.mk (fun n n' _ =>
      HomologicalComplex.mapBifunctorDesc (fun p q (_ : p + q = n) =>
        (p : ℤ).negOnePow • ((curriedTensor C).obj (G.X p)).map
            ((CochainComplex.mappingCone.fst φ).1.v q (q+1) (by omega)) ≫
          HomologicalComplex.ιMapBifunctor G K (curriedTensor C) (ComplexShape.up ℤ) p (q+1) n'
            (by change p + (q+1) = n'; omega)))
  let bCoch : CochainComplex.HomComplex.Cochain
      ((TleftCochain G).obj (CochainComplex.mappingCone φ))
      ((TleftCochain G).obj L) 0 :=
    CochainComplex.HomComplex.Cochain.mk (fun n n' _ =>
      HomologicalComplex.mapBifunctorDesc (fun p q (_ : p + q = n) =>
        ((curriedTensor C).obj (G.X p)).map
            ((CochainComplex.mappingCone.snd φ).v q q (by omega)) ≫
          HomologicalComplex.ιMapBifunctor G L (curriedTensor C) (ComplexShape.up ℤ) p q n'
            (by change p + q = n'; omega)))
  have ha : CochainComplex.HomComplex.δ 1 2 aCoch = 0 := by
    ext n n' h
    subst h
    rw [CochainComplex.HomComplex.δ_v 1 2 (by omega) aCoch n (n+2) (by omega) (n+1) (n+1)
      (by omega) (by omega)]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpqn : p + q = n := hpq
    rw [Preadditive.comp_add, ← Category.assoc]
    simp only [aCoch, CochainComplex.HomComplex.Cochain.mk_v, HomologicalComplex.ι_mapBifunctorDesc,
      Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc]
    have dK : ((TleftCochain G).obj K).d (n+1) (n+2)
        = HomologicalComplex.mapBifunctor.D₁ G K (curriedTensor C) (ComplexShape.up ℤ) (n+1) (n+2)
          + HomologicalComplex.mapBifunctor.D₂ G K (curriedTensor C)
              (ComplexShape.up ℤ) (n+1) (n+2) :=
      HomologicalComplex.mapBifunctor.d_eq G K (curriedTensor C) (ComplexShape.up ℤ) (n+1) (n+2)
    have dX : ((TleftCochain G).obj (CochainComplex.mappingCone φ)).d n (n+1)
        = HomologicalComplex.mapBifunctor.D₁ G (CochainComplex.mappingCone φ) (curriedTensor C)
            (ComplexShape.up ℤ) n (n+1)
          + HomologicalComplex.mapBifunctor.D₂ G (CochainComplex.mappingCone φ) (curriedTensor C)
              (ComplexShape.up ℤ) n (n+1) :=
      HomologicalComplex.mapBifunctor.d_eq G (CochainComplex.mappingCone φ) (curriedTensor C)
        (ComplexShape.up ℤ) n (n+1)
    rw [dK, dX]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq G K (curriedTensor C) (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel p (p+1) by rw [ComplexShape.up_Rel]) (q+1) (n+2)
        (by change (p+1)+(q+1)=n+2; omega),
      HomologicalComplex.mapBifunctor.d₂_eq G K (curriedTensor C) (ComplexShape.up ℤ) p
        (show (ComplexShape.up ℤ).Rel (q+1) (q+1+1) by rw [ComplexShape.up_Rel]) (n+2)
        (by change p+(q+1+1)=n+2; omega),
      HomologicalComplex.mapBifunctor.d₁_eq G (CochainComplex.mappingCone φ) (curriedTensor C)
        (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel p (p+1) by rw [ComplexShape.up_Rel])
        q (n+1) (by change (p+1)+q=n+1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq G (CochainComplex.mappingCone φ) (curriedTensor C)
        (ComplexShape.up ℤ) p (show (ComplexShape.up ℤ).Rel q (q+1) by rw [ComplexShape.up_Rel])
        (n+1) (by change p+(q+1)=n+1; omega)]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    rw [show (0 : CochainComplex.HomComplex.Cochain
        ((TleftCochain G).obj (CochainComplex.mappingCone φ))
        ((TleftCochain G).obj K) 2).v n (n+2) (by omega) = 0 from rfl, comp_zero]
    rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q+1) = 1 from rfl,
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q+1)
        = (p:ℤ).negOnePow from rfl,
      show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = 1 from rfl,
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q)
        = (p:ℤ).negOnePow from rfl]
    rw [← NatTrans.naturality_assoc ((curriedTensor C).map (G.d p (p+1)))
        ((CochainComplex.mappingCone.fst φ).1.v q (q+1) (by omega)),
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      CochainComplex.mappingCone.d_fst_v φ q (q+1) (q+1+1) (by omega) (by omega)]
    have e2 : (2 : ℤ).negOnePow = 1 := by decide
    have ep : (p + 1 : ℤ).negOnePow = - (p:ℤ).negOnePow := by rw [Int.negOnePow_succ]
    rw [e2, ep]
    simp only [one_smul, Functor.map_neg, Functor.map_comp, Preadditive.neg_comp,
       Category.assoc, Units.neg_smul, smul_add,
      smul_smul, Int.units_mul_self]
    abel
  have hab : CochainComplex.HomComplex.δ 0 1 bCoch +
      (aCoch).comp (CochainComplex.HomComplex.Cochain.ofHom ((TleftCochain G).map φ)) (by omega)
      = 0 := by
    ext n n' h
    subst h
    rw [CochainComplex.HomComplex.Cochain.add_v,
      CochainComplex.HomComplex.δ_v 0 1 (by omega) bCoch n (n+1) (by omega) n (n+1)
        (by omega) (by omega),
      CochainComplex.HomComplex.Cochain.comp_v aCoch
        (CochainComplex.HomComplex.Cochain.ofHom ((TleftCochain G).map φ)) (by omega) n (n+1)
        (n+1) (by omega) (by omega),
      CochainComplex.HomComplex.Cochain.ofHom_v]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpqn : p + q = n := hpq
    rw [Preadditive.comp_add, Preadditive.comp_add]
    have dL : ((TleftCochain G).obj L).d n (n+1)
        = HomologicalComplex.mapBifunctor.D₁ G L (curriedTensor C) (ComplexShape.up ℤ) n (n+1)
          + HomologicalComplex.mapBifunctor.D₂ G L (curriedTensor C) (ComplexShape.up ℤ) n (n+1) :=
      HomologicalComplex.mapBifunctor.d_eq G L (curriedTensor C) (ComplexShape.up ℤ) n (n+1)
    have dX : ((TleftCochain G).obj (CochainComplex.mappingCone φ)).d n (n+1)
        = HomologicalComplex.mapBifunctor.D₁ G (CochainComplex.mappingCone φ) (curriedTensor C)
            (ComplexShape.up ℤ) n (n+1)
          + HomologicalComplex.mapBifunctor.D₂ G (CochainComplex.mappingCone φ) (curriedTensor C)
              (ComplexShape.up ℤ) n (n+1) :=
      HomologicalComplex.mapBifunctor.d_eq G (CochainComplex.mappingCone φ) (curriedTensor C)
        (ComplexShape.up ℤ) n (n+1)
    have hTφ : ((TleftCochain G).map φ)
        = HomologicalComplex.mapBifunctorMap (𝟙 G) φ (curriedTensor C) (ComplexShape.up ℤ) := rfl
    rw [hTφ]
    rw [← Category.assoc (HomologicalComplex.ιMapBifunctor G (CochainComplex.mappingCone φ)
        (curriedTensor C) (ComplexShape.up ℤ) p q n hpq),
      ← Category.assoc (HomologicalComplex.ιMapBifunctor G (CochainComplex.mappingCone φ)
          (curriedTensor C) (ComplexShape.up ℤ) p q n hpq) _
        ((HomologicalComplex.mapBifunctorMap (𝟙 G) φ (curriedTensor C)
          (ComplexShape.up ℤ)).f (n+1))]
    simp only [bCoch, aCoch, CochainComplex.HomComplex.Cochain.mk_v,
      HomologicalComplex.ι_mapBifunctorDesc, Linear.units_smul_comp]
    rw [dL, dX]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc,
      Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
      Linear.comp_units_smul, Preadditive.comp_add]
    rw [HomologicalComplex.mapBifunctor.d₁_eq G L (curriedTensor C) (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel p (p+1) by rw [ComplexShape.up_Rel]) q (n+1)
        (by change (p+1)+q=n+1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq G L (curriedTensor C) (ComplexShape.up ℤ) p
        (show (ComplexShape.up ℤ).Rel q (q+1) by rw [ComplexShape.up_Rel]) (n+1)
        (by change p+(q+1)=n+1; omega),
      HomologicalComplex.mapBifunctor.d₁_eq G (CochainComplex.mappingCone φ) (curriedTensor C)
        (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel p (p+1) by rw [ComplexShape.up_Rel])
        q (n+1) (by change (p+1)+q=n+1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq G (CochainComplex.mappingCone φ) (curriedTensor C)
        (ComplexShape.up ℤ) p (show (ComplexShape.up ℤ).Rel q (q+1) by rw [ComplexShape.up_Rel])
        (n+1) (by change p+(q+1)=n+1; omega)]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    rw [show (0 : CochainComplex.HomComplex.Cochain
        ((TleftCochain G).obj (CochainComplex.mappingCone φ))
        ((TleftCochain G).obj L) 1).v n (n+1) (by omega) = 0 from rfl, comp_zero]
    rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = 1 from rfl,
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q)
        = (p:ℤ).negOnePow from rfl]
    rw [← NatTrans.naturality_assoc ((curriedTensor C).map (G.d p (p+1)))
        ((CochainComplex.mappingCone.snd φ).v q q (by omega)),
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      CochainComplex.mappingCone.d_snd_v φ q (q+1) (by omega)]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, Functor.map_add, Functor.map_comp, Preadditive.add_comp,
      Category.assoc, one_smul, Int.negOnePow_one, Units.neg_smul, smul_add, smul_smul,
       one_mul, neg_mul]
    abel
  exact CochainComplex.mappingCone.lift ((TleftCochain G).map φ)
    (CochainComplex.HomComplex.Cocycle.mk aCoch 2 (by omega) ha) bCoch hab

/-- **Θ.inv** (the backward cone-commutation map).

A morphism `C(Tot(id_G ⊗ φ)) ⟶ Tot(G ⊗ C(φ))`. By `mappingCone.desc` (universal property of the
*domain* cone `C(Tot(id_G ⊗ φ))`), determined by a degree-`(-1)` cochain
`α' : Cochain (Tot(G⊗K)) (Tot(G⊗C(φ))) (-1)` (= `alphaPrime`, the `K`-component, sign
`(q).negOnePow` on inner index, validated by the prior closer) and a degree-`0` morphism
`β' = (TleftCochain G).map (mappingCone.inr φ) : Tot(G⊗L) ⟶ Tot(G⊗C(φ))`, satisfying the desc
δ-condition `δ (-1) 0 α' = ofHom ((TleftCochain G).map φ ≫ β')`. -/
noncomputable def TleftCochain_mappingCone_inv (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    CochainComplex.mappingCone ((TleftCochain G).map φ) ⟶
      (TleftCochain G).obj (CochainComplex.mappingCone φ) := by
  -- Build via `CochainComplex.mappingCone.desc _ alphaPrime β hαβ` with
  -- `β = (TleftCochain G).map (CochainComplex.mappingCone.inr φ)` and `alphaPrime` the K-component
  -- (sign `(p).negOnePow`), `hαβ` the desc δ-condition.
  let alphaPrime : CochainComplex.HomComplex.Cochain ((TleftCochain G).obj K)
      ((TleftCochain G).obj (CochainComplex.mappingCone φ)) (-1) :=
    CochainComplex.HomComplex.Cochain.mk (fun n n' _ =>
      HomologicalComplex.mapBifunctorDesc (fun p q (_ : p + q = n) =>
        (p : ℤ).negOnePow • ((curriedTensor C).obj (G.X p)).map
            ((CochainComplex.mappingCone.inl φ).v q (q-1) (by omega)) ≫
          HomologicalComplex.ιMapBifunctor G (CochainComplex.mappingCone φ) (curriedTensor C)
            (ComplexShape.up ℤ) p (q-1) n'
            (by change p + (q-1) = n'; omega)))
  have hTφ : ((TleftCochain G).map φ)
      = HomologicalComplex.mapBifunctorMap (𝟙 G) φ (curriedTensor C) (ComplexShape.up ℤ) := rfl
  have hαβ : CochainComplex.HomComplex.δ (-1) 0 alphaPrime
      = CochainComplex.HomComplex.Cochain.ofHom
          ((TleftCochain G).map φ ≫ (TleftCochain G).map (CochainComplex.mappingCone.inr φ)) := by
    ext n
    rw [CochainComplex.HomComplex.δ_v (-1) 0 (by omega) alphaPrime n n (by omega) (n-1) (n+1)
        (by omega) (by omega),
      CochainComplex.HomComplex.Cochain.ofHom_v]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpqn : p + q = n := hpq
    rw [Preadditive.comp_add, ← Category.assoc]
    simp only [alphaPrime, CochainComplex.HomComplex.Cochain.mk_v,
      HomologicalComplex.ι_mapBifunctorDesc, Linear.units_smul_comp, Linear.comp_units_smul,
      Category.assoc]
    have dK : ((TleftCochain G).obj K).d n (n+1)
        = HomologicalComplex.mapBifunctor.D₁ G K (curriedTensor C) (ComplexShape.up ℤ) n (n+1)
          + HomologicalComplex.mapBifunctor.D₂ G K (curriedTensor C) (ComplexShape.up ℤ) n (n+1) :=
      HomologicalComplex.mapBifunctor.d_eq G K (curriedTensor C) (ComplexShape.up ℤ) n (n+1)
    have dXc : ((TleftCochain G).obj (CochainComplex.mappingCone φ)).d (n-1) n
        = HomologicalComplex.mapBifunctor.D₁ G (CochainComplex.mappingCone φ) (curriedTensor C)
            (ComplexShape.up ℤ) (n-1) n
          + HomologicalComplex.mapBifunctor.D₂ G (CochainComplex.mappingCone φ) (curriedTensor C)
              (ComplexShape.up ℤ) (n-1) n :=
      HomologicalComplex.mapBifunctor.d_eq G (CochainComplex.mappingCone φ) (curriedTensor C)
        (ComplexShape.up ℤ) (n-1) n
    rw [dK, dXc]
    simp only [Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    rw [HomologicalComplex.mapBifunctor.d₁_eq G (CochainComplex.mappingCone φ) (curriedTensor C)
        (ComplexShape.up ℤ) (show (ComplexShape.up ℤ).Rel p (p+1) by rw [ComplexShape.up_Rel])
        (q-1) n (by change (p+1)+(q-1)=n; omega),
      HomologicalComplex.mapBifunctor.d₂_eq G (CochainComplex.mappingCone φ) (curriedTensor C)
        (ComplexShape.up ℤ) p
        (show (ComplexShape.up ℤ).Rel (q-1) q by rw [ComplexShape.up_Rel]; omega) n
        (by change p+q=n; omega),
      HomologicalComplex.mapBifunctor.d₁_eq G K (curriedTensor C) (ComplexShape.up ℤ)
        (show (ComplexShape.up ℤ).Rel p (p+1) by rw [ComplexShape.up_Rel]) q (n+1)
        (by change (p+1)+q=n+1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq G K (curriedTensor C) (ComplexShape.up ℤ) p
        (show (ComplexShape.up ℤ).Rel q (q+1) by rw [ComplexShape.up_Rel]) (n+1)
        (by change p+(q+1)=n+1; omega)]
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
      HomologicalComplex.ι_mapBifunctorDesc]
    rw [hTφ]
    simp only [HomologicalComplex.comp_f]
    rw [show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q-1) = 1 from rfl,
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q-1)
        = (p:ℤ).negOnePow from rfl,
      show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = 1 from rfl,
      show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q)
        = (p:ℤ).negOnePow from rfl]
    rw [← NatTrans.naturality_assoc ((curriedTensor C).map (G.d p (p+1)))
        ((CochainComplex.mappingCone.inl φ).v q (q-1) (by omega)),
      ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
      CochainComplex.mappingCone.inl_v_d φ q (q-1) (q+1) (by omega) (by omega)]
    have e0 : (0 : ℤ).negOnePow = 1 := by decide
    have ep : (p + 1 : ℤ).negOnePow = - (p:ℤ).negOnePow := by rw [Int.negOnePow_succ]
    rw [e0, ep]
    simp only [Functor.map_sub, Functor.map_comp, Preadditive.sub_comp,
       Category.assoc,
      one_smul, Units.neg_smul, smul_add, smul_sub, smul_smul,
      Int.units_mul_self]
    have hTinr : (TleftCochain G).map (CochainComplex.mappingCone.inr φ)
        = HomologicalComplex.mapBifunctorMap (𝟙 G) (CochainComplex.mappingCone.inr φ)
            (curriedTensor C) (ComplexShape.up ℤ) := rfl
    rw [hTinr]
    rw [← Category.assoc (HomologicalComplex.ιMapBifunctor G K (curriedTensor C)
      (ComplexShape.up ℤ) p q n hpq)]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.assoc]
    rw [HomologicalComplex.ι_mapBifunctorMap]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp]
    have hcancel :
        ((curriedTensor C).obj (G.X p)).map (K.d q (q + 1)) ≫
          ((curriedTensor C).obj (G.X p)).map
              ((CochainComplex.mappingCone.inl φ).v (q + 1) (q + 1 - 1) (by omega)) ≫
            HomologicalComplex.ιMapBifunctor G (CochainComplex.mappingCone φ) (curriedTensor C)
              (ComplexShape.up ℤ) p (q + 1 - 1) n (by change p + (q+1-1) = n; omega)
      = ((curriedTensor C).obj (G.X p)).map (K.d q (q + 1)) ≫
          ((curriedTensor C).obj (G.X p)).map
              ((CochainComplex.mappingCone.inl φ).v (q + 1) q (by omega)) ≫
            HomologicalComplex.ιMapBifunctor G (CochainComplex.mappingCone φ) (curriedTensor C)
              (ComplexShape.up ℤ) p q n (by change p + q = n; omega) := by
      congr! 3
      all_goals (try omega)
      · rw [show (q : ℤ) + 1 - 1 = q from by omega]
      · rw [show (q : ℤ) + 1 - 1 = q from by omega]
      · simp only [CochainComplex.HomComplex.Cochain.v]
        congr 1
        congr 1
        omega
    rw [hcancel]
    abel
  exact CochainComplex.mappingCone.desc ((TleftCochain G).map φ) alphaPrime
    ((TleftCochain G).map (CochainComplex.mappingCone.inr φ)) hαβ

omit [HasZeroObject C] in
/-- `Θ.hom ≫ Θ.inv = 𝟙` (degreewise biproduct computation: the diagonal
scalar blocks are `ε(p)·ε(p)=1` on K-summands and `1` on L-summands). Use `mappingCone.id` /
`ext_from_X` (`mapBifunctor.hom_ext`) + `lift_desc_f`. -/
theorem TleftCochain_mappingCone_hom_inv (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    TleftCochain_mappingCone_hom G φ ≫ TleftCochain_mappingCone_inv G φ = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  unfold TleftCochain_mappingCone_hom TleftCochain_mappingCone_inv
  rw [CochainComplex.mappingCone.lift_desc_f _ _ _ _ _ _ _ n (n+1) (by omega)]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hpqn : p + q = n := hpq
  simp only [CochainComplex.HomComplex.Cocycle.mk_coe,
    CochainComplex.HomComplex.Cochain.mk_v]
  rw [Preadditive.comp_add]
  -- K-term
  rw [← Category.assoc (HomologicalComplex.ιMapBifunctor G (CochainComplex.mappingCone φ)
      (curriedTensor C) (ComplexShape.up ℤ) p q n hpq),
    HomologicalComplex.ι_mapBifunctorDesc]
  rw [Linear.units_smul_comp, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
  -- L-term: rewrite (TleftCochain G).map (inr φ) as mapBifunctorMap
  have hTinr : (TleftCochain G).map (CochainComplex.mappingCone.inr φ)
      = HomologicalComplex.mapBifunctorMap (𝟙 G) (CochainComplex.mappingCone.inr φ)
          (curriedTensor C) (ComplexShape.up ℤ) := rfl
  rw [hTinr,
    ← Category.assoc (HomologicalComplex.ιMapBifunctor G (CochainComplex.mappingCone φ)
      (curriedTensor C) (ComplexShape.up ℤ) p q n hpq),
    HomologicalComplex.ι_mapBifunctorDesc, Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp]
  rw [Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul]
  -- Normalize the K-term index `q+1-1` to `q`.
  have hcancel :
      ((curriedTensor C).obj (G.X p)).map
          ((CochainComplex.mappingCone.inl φ).v (q + 1) (q + 1 - 1) (by omega)) ≫
          HomologicalComplex.ιMapBifunctor G (CochainComplex.mappingCone φ) (curriedTensor C)
            (ComplexShape.up ℤ) p
            (q + 1 - 1) n (by change p + (q+1-1) = n; omega)
        = ((curriedTensor C).obj (G.X p)).map
            ((CochainComplex.mappingCone.inl φ).v (q + 1) q (by omega)) ≫
          HomologicalComplex.ιMapBifunctor G (CochainComplex.mappingCone φ) (curriedTensor C)
            (ComplexShape.up ℤ) p
            q n (by change p + q = n; omega) := by
      congr! 3
      all_goals (try omega)
  rw [hcancel]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← Preadditive.add_comp,
    ← Functor.map_add, CochainComplex.mappingCone.id_X φ q (q+1) (by omega),
    CategoryTheory.Functor.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

omit [HasZeroObject C] in
/-- `Θ.inv ≫ Θ.hom = 𝟙` (mirror degreewise biproduct computation). Use
`mappingCone.ext_to_X` / `mappingCone.id` + `lift_desc_f`. -/
theorem TleftCochain_mappingCone_inv_hom (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    TleftCochain_mappingCone_inv G φ ≫ TleftCochain_mappingCone_hom G φ = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  unfold TleftCochain_mappingCone_inv TleftCochain_mappingCone_hom
  apply CochainComplex.mappingCone.ext_from ((TleftCochain G).map φ) (n+1) n (by omega)
  · rw [← Category.assoc, CochainComplex.mappingCone.inl_v_desc_f]
    rw [Category.comp_id]
    simp only [CochainComplex.HomComplex.Cochain.mk_v]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpqn : p + q = n + 1 := hpq
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc]
    rw [Linear.units_smul_comp]
    rw [CochainComplex.mappingCone.lift_f ((TleftCochain G).map φ) _ _ _ n (n+1) (by omega)]
    simp only [CochainComplex.HomComplex.Cocycle.mk_coe,
      CochainComplex.HomComplex.Cochain.mk_v]
    rw [Preadditive.comp_add]
    -- K-term (aCoch via fst): inl φ ≫ fst φ
    rw [Category.assoc, ← Category.assoc (HomologicalComplex.ιMapBifunctor G
        (CochainComplex.mappingCone φ) (curriedTensor C) (ComplexShape.up ℤ) p (q-1) n
        (by change p + (q-1) = n; omega)),
      HomologicalComplex.ι_mapBifunctorDesc]
    -- L-term (bCoch via snd): inl φ ≫ snd φ
    rw [Category.assoc, ← Category.assoc (HomologicalComplex.ιMapBifunctor G
        (CochainComplex.mappingCone φ) (curriedTensor C) (ComplexShape.up ℤ) p (q-1) n
        (by change p + (q-1) = n; omega)),
      HomologicalComplex.ι_mapBifunctorDesc]
    -- Normalize: pull all sign scalars out, associate
    simp only [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
      ]
    -- merge map(inl φ) ≫ map(fst φ) = 𝟙, map(inl φ) ≫ map(snd φ) = 0
    have hsnd : (CochainComplex.mappingCone.inl φ).v q (q-1) (by omega) ≫
        (CochainComplex.mappingCone.snd φ).v (q-1) (q-1) (by omega) = 0 :=
      CochainComplex.mappingCone.inl_v_snd_v φ q (q-1) (by omega)
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hsnd,
      CategoryTheory.Functor.map_zero, Limits.zero_comp, add_zero]
    -- K-term: normalize the inner index q-1+1 → q so inl;fst collapses to 𝟙
    have hcancel :
        ((curriedTensor C).obj (G.X p)).map
              ((CochainComplex.mappingCone.inl φ).v q (q-1) (by omega) ≫
                (CochainComplex.mappingCone.fst φ).1.v (q-1) (q-1+1) (by omega)) ≫
            HomologicalComplex.ιMapBifunctor G K (curriedTensor C) (ComplexShape.up ℤ) p (q-1+1)
              (n+1) (by change p + (q-1+1) = n+1; omega) ≫
            (CochainComplex.mappingCone.inl ((TleftCochain G).map φ)).v (n+1) n (by omega)
          = ((curriedTensor C).obj (G.X p)).map
              ((CochainComplex.mappingCone.inl φ).v q (q-1) (by omega) ≫
                (CochainComplex.mappingCone.fst φ).1.v (q-1) q (by omega)) ≫
            HomologicalComplex.ιMapBifunctor G K (curriedTensor C) (ComplexShape.up ℤ) p q (n+1)
              hpq ≫
            (CochainComplex.mappingCone.inl ((TleftCochain G).map φ)).v (n+1) n (by omega) := by
      congr! 3
      all_goals first | omega | (congr 1; (try omega); (try exact proof_irrel_heq _ _))
    rw [hcancel, CochainComplex.mappingCone.inl_v_fst_v φ q (q-1) (by omega),
      CategoryTheory.Functor.map_id, Category.id_comp, smul_smul, Int.units_mul_self, one_smul]
  · rw [← Category.assoc, CochainComplex.mappingCone.inr_f_desc_f]
    rw [Category.comp_id]
    have hTinr : (TleftCochain G).map (CochainComplex.mappingCone.inr φ)
        = HomologicalComplex.mapBifunctorMap (𝟙 G) (CochainComplex.mappingCone.inr φ)
            (curriedTensor C) (ComplexShape.up ℤ) := rfl
    rw [hTinr]
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpqn : p + q = n := hpq
    rw [← Category.assoc (HomologicalComplex.ιMapBifunctor G L (curriedTensor C)
        (ComplexShape.up ℤ) p q n hpq),
      HomologicalComplex.ι_mapBifunctorMap]
    rw [CochainComplex.mappingCone.lift_f ((TleftCochain G).map φ) _ _ _ n (n+1) (by omega)]
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp, Category.assoc]
    simp only [CochainComplex.HomComplex.Cocycle.mk_coe,
      CochainComplex.HomComplex.Cochain.mk_v]
    rw [Preadditive.comp_add]
    -- K-term (aCoch via fst): inr φ ≫ fst φ = 0 ;  L-term (bCoch via snd): inr φ ≫ snd φ = 𝟙
    rw [HomologicalComplex.ι_mapBifunctorDesc_assoc, HomologicalComplex.ι_mapBifunctorDesc_assoc]
    rw [Preadditive.comp_add]
    rw [Linear.units_smul_comp, Linear.comp_units_smul,
      Category.assoc, ← Functor.map_comp_assoc,
      CochainComplex.mappingCone.inr_f_fst_v φ q (q+1) (by omega),
      CategoryTheory.Functor.map_zero, Limits.zero_comp, smul_zero, zero_add]
    rw [Category.assoc, ← Functor.map_comp_assoc, CochainComplex.mappingCone.inr_f_snd_v φ q,
      CategoryTheory.Functor.map_id, Category.id_comp]

/-- The isomorphism of cochain complexes `Tot(G ⊗ C(φ)) ≅ C(Tot(id_G ⊗ φ))` between the image under
`TleftCochain G` of the mapping cone of `φ` and the mapping cone of `(TleftCochain G).map φ`. -/
noncomputable def TleftCochain_mappingCone_iso (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    (TleftCochain G).obj (CochainComplex.mappingCone φ) ≅
      CochainComplex.mappingCone ((TleftCochain G).map φ) where
  hom := TleftCochain_mappingCone_hom G φ
  inv := TleftCochain_mappingCone_inv G φ
  hom_inv_id := TleftCochain_mappingCone_hom_inv G φ
  inv_hom_id := TleftCochain_mappingCone_inv_hom G φ

omit [HasZeroObject C] in
/-- The image under `TleftCochain G` of the mapping-cone triangle of `φ` is isomorphic to the
mapping-cone triangle of `(TleftCochain G).map φ`. -/
theorem TleftCochain_mapTriangle_triangle_iso (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    letI : (TleftCochain G).CommShift ℤ := by unfold TleftCochain; infer_instance
    Nonempty ((TleftCochain G).mapTriangle.obj (CochainComplex.mappingCone.triangle φ) ≅
      CochainComplex.mappingCone.triangle ((TleftCochain G).map φ)) := by
  let : (TleftCochain G).CommShift ℤ := by unfold TleftCochain; infer_instance
  have hinr : CochainComplex.mappingCone.inr ((TleftCochain G).map φ) ≫
      (TleftCochain_mappingCone_iso G φ).inv
      = (TleftCochain G).map (CochainComplex.mappingCone.inr φ) := by
    simp only [TleftCochain_mappingCone_iso]
    unfold TleftCochain_mappingCone_inv
    rw [CochainComplex.mappingCone.inr_desc]
  refine ⟨CategoryTheory.Pretriangulated.Triangle.isoMk _ _
    (Iso.refl _) (Iso.refl _) (TleftCochain_mappingCone_iso G φ) ?_ ?_ ?_⟩
  · -- mor₁ compatibility: `φ` vs `Tot(id_G ⊗ φ) = (TleftCochain G).map φ` (sign-free).
    -- `Functor.mapTriangle_obj` no longer rewrites here (the `Iso.refl _` objects make the
    -- rewrite motive ill-typed under the stricter transparency), so we finish via defeq `rfl`.
    simp only [CochainComplex.mappingCone.triangle_mor₁,
      Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl
  · -- mor₂ compatibility: the `inr` inclusions (sign-free L-summand) intertwine via Θ.
    simp only [CochainComplex.mappingCone.triangle_mor₂, Iso.refl_hom, Category.id_comp]
    -- expose the (defeq) reduced form of `(mapTriangle.obj _).mor₂`
    show (TleftCochain G).map (CochainComplex.mappingCone.inr φ)
        ≫ (TleftCochain_mappingCone_iso G φ).hom
      = CochainComplex.mappingCone.inr ((TleftCochain G).map φ)
    rw [← hinr, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · -- mor₃ compatibility: the connecting map δ = (-fst).rightShift 1; the K-summand sign ε(q)
    -- and `commShiftIso (TleftCochain G) 1 = mapBifunctorShift₂Iso` enter here.
    simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id]
    -- expose the (defeq) reduced form of `(mapTriangle.obj _).mor₃`
    show (TleftCochain G).map (CochainComplex.mappingCone.triangle φ).mor₃
        ≫ (Functor.commShiftIso (TleftCochain G) 1).hom.app
            (CochainComplex.mappingCone.triangle φ).obj₁
      = (TleftCochain_mappingCone_iso G φ).hom
        ≫ (CochainComplex.mappingCone.triangle ((TleftCochain G).map φ)).mor₃
    rw [← Iso.inv_comp_eq]
    apply HomologicalComplex.hom_ext
    intro n
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
    apply CochainComplex.mappingCone.ext_from ((TleftCochain G).map φ) (n+1) n rfl
    · -- h₁: inl-summand (K-component). The sign ε and commShiftIso enter here.
      rw [CochainComplex.mappingCone.inl_v_triangle_mor₃_f]
      rw [← Category.assoc
        ((CochainComplex.mappingCone.inl ((TleftCochain G).map φ)).v (n+1) n (by omega))]
      have hinl : (CochainComplex.mappingCone.inl ((TleftCochain G).map φ)).v (n+1) n (by omega)
            ≫ (TleftCochain_mappingCone_iso G φ).inv.f n
          = HomologicalComplex.mapBifunctorDesc (fun p q (_ : p + q = (n+1)) =>
              (p : ℤ).negOnePow • ((curriedTensor C).obj (G.X p)).map
                ((CochainComplex.mappingCone.inl φ).v q (q-1) (by omega)) ≫
              HomologicalComplex.ιMapBifunctor G (CochainComplex.mappingCone φ) (curriedTensor C)
                (ComplexShape.up ℤ) p (q-1) n
                (by change p + (q-1) = n; omega)) := by
        simp only [TleftCochain_mappingCone_iso]
        unfold TleftCochain_mappingCone_inv
        rw [CochainComplex.mappingCone.inl_v_desc_f]
        rfl
      rw [hinl]
      apply HomologicalComplex.mapBifunctor.hom_ext
      intro p q hpq
      have hpqn : p + q = n + 1 := hpq
      rw [← Category.assoc, ← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
      have hTδ : ((TleftCochain G).map (CochainComplex.mappingCone.triangle φ).mor₃)
          = HomologicalComplex.mapBifunctorMap (𝟙 G) (CochainComplex.mappingCone.triangle φ).mor₃
              (curriedTensor C) (ComplexShape.up ℤ) := rfl
      rw [Linear.units_smul_comp, Category.assoc, hTδ,
        HomologicalComplex.ι_mapBifunctorMap]
      simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
        Category.id_comp]
      have hcs : ((Functor.commShiftIso (TleftCochain G) 1).hom.app
            (CochainComplex.mappingCone.triangle φ).obj₁)
          = (CochainComplex.mapBifunctorShift₂Iso G (CochainComplex.mappingCone.triangle φ).obj₁
              (curriedTensor C) 1).hom := rfl
      rw [Linear.units_smul_comp, Category.assoc, Category.assoc, hcs,
        CochainComplex.ι_mapBifunctorShift₂Iso_hom_f G (CochainComplex.mappingCone.triangle φ).obj₁
          (curriedTensor C) 1 p (q-1) n
          (by show p + (q-1) = n; omega) q (n+1) (by omega) (by omega)]
      rw [Linear.comp_units_smul, Linear.comp_units_smul]
      rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
      rw [CochainComplex.mappingCone.inl_v_triangle_mor₃_f, Preadditive.neg_comp]
      have hih : (K.shiftFunctorObjXIso 1 (q - 1) q (by omega)).inv ≫
          ((CochainComplex.mappingCone.triangle φ).obj₁.shiftFunctorObjXIso 1 (q - 1) q
            (by omega)).hom
          = 𝟙 _ := Iso.inv_hom_id _
      rw [hih, CategoryTheory.Functor.map_neg, CategoryTheory.Functor.map_id,
        Preadditive.neg_comp, Category.id_comp]
      rw [smul_neg, smul_neg, mul_one, smul_smul, Int.units_mul_self, one_smul]
      rw [Preadditive.comp_neg]
      rfl
    · -- h₂: inr-summand. Both sides are 0.
      rw [CochainComplex.mappingCone.inr_f_triangle_mor₃_f]
      rw [← Category.assoc, ← Category.assoc, ← HomologicalComplex.comp_f,
        hinr]
      rw [← HomologicalComplex.comp_f, ← Functor.map_comp]
      have h0 : (CochainComplex.mappingCone.inr φ) ≫
          (CochainComplex.mappingCone.triangle φ).mor₃ = 0 := by
        apply HomologicalComplex.hom_ext
        intro m
        rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
          CochainComplex.mappingCone.inr_f_triangle_mor₃_f]
      rw [h0, CategoryTheory.Functor.map_zero, HomologicalComplex.zero_f, Limits.zero_comp]

omit [HasZeroObject C] in
/-- **Descent glue (routine modulo `TleftCochain_mapTriangle_triangle_iso`).**

Pushes the cochain-level cone-commutation triangle iso through the homotopy-category quotient
`Q = HomotopyCategory.quotient`, using that `triangleh ψ = Q.mapTriangle.obj (triangle ψ)`
(an abbrev) and the strict lift iso `Q ⋙ Tleft G ≅ TleftCochain G ⋙ Q`
(`CategoryTheory.Quotient.lift.isLift`), via `Functor.mapTriangleCompIso` and
`Functor.mapTriangleIso`. The single nontrivial Lean obligation is supplying the
`NatTrans.CommShift` datum of the lift iso (from `Quotient.liftCommShift_compatibility`)
so that `Functor.mapTriangleIso` applies. -/
theorem Tleft_mapTriangle_triangleh_iso (G : CochainComplex C ℤ)
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) :
    letI := TleftCommShift G
    Nonempty ((Tleft G).mapTriangle.obj (CochainComplex.mappingCone.triangleh φ) ≅
      CochainComplex.mappingCone.triangleh ((TleftCochain G).map φ)) := by
  let := TleftCommShift G
  let hcs : (TleftCochain G).CommShift ℤ := by unfold TleftCochain; infer_instance
  -- SANITY CHECK PASSED
  -- Step A (analytic kernel): the cochain-level cone-commutation triangle iso.
  obtain ⟨Φ⟩ := TleftCochain_mapTriangle_triangle_iso G φ
  refine ⟨?_⟩
  -- `triangleh ψ = Q.mapTriangle.obj (triangle ψ)` (abbrev, rfl); apply `Q.mapTriangle.mapIso Φ`
  -- after rewriting the LHS through the strict lift iso `Q ⋙ Tleft G ≅ TleftCochain G ⋙ Q`.
  refine ?_ ≪≫ (HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapTriangle.mapIso Φ
  refine (Functor.mapTriangleCompIso _ _).symm.app _ ≪≫ ?_ ≪≫ (Functor.mapTriangleCompIso _ _).app _
  show ((HomotopyCategory.quotient C (ComplexShape.up ℤ)) ⋙ Tleft G).mapTriangle.obj _ ≅
       ((TleftCochain G) ⋙ (HomotopyCategory.quotient C (ComplexShape.up ℤ))).mapTriangle.obj _
  -- The strict lift iso, with its `NatTrans.CommShift` datum
  -- (`Quotient.liftCommShift_compatibility`).
  -- Build the strict lift iso EXPLICITLY as `Quotient.lift.isLift`, so that the
  -- `NatTrans.CommShift` compatibility instance fires syntactically.
  let : (TleftCochain G ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ)).CommShift ℤ :=
    inferInstance
  let hlift : (HomotopyCategory.quotient C (ComplexShape.up ℤ)) ⋙ Tleft G ≅
      (TleftCochain G) ⋙ (HomotopyCategory.quotient C (ComplexShape.up ℤ)) :=
    CategoryTheory.Quotient.lift.isLift (homotopic C (ComplexShape.up ℤ))
      (TleftCochain G ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ))
      (fun _ _ _ _ h => CategoryTheory.Quotient.sound _ (TleftCochain_preservesHomotopyRel G h))
  have : NatTrans.CommShift hlift.hom ℤ :=
    CategoryTheory.Quotient.liftCommShift_compatibility
      (TleftCochain G ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ))
      (homotopic C (ComplexShape.up ℤ)) ℤ _
  exact (Functor.mapTriangleIso hlift).app _

/-- The functor `Tleft G` sends distinguished triangles of the homotopy category `K(C)` to
distinguished triangles. -/
@[sga "4 XVII 7.3.3" "special case"]
theorem Tleft_mapTriangle_distinguished (G : CochainComplex C ℤ)
    (T : Triangle (HomotopyCategory C (ComplexShape.up ℤ)))
    (hT : T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ))) :
    letI := TleftCommShift G
    (Tleft G).mapTriangle.obj T ∈ distTriang (HomotopyCategory C (ComplexShape.up ℤ)) := by
  let := TleftCommShift G
  -- Every distinguished triangle of `K(C)` is, up to isomorphism, `triangleh φ`.
  obtain ⟨K, L, φ, ⟨e⟩⟩ := hT
  -- The cone-commutation isomorphism gives a triangle isomorphism to `triangleh (Tot(id_G ⊗ φ))`.
  obtain ⟨ι⟩ := Tleft_mapTriangle_triangleh_iso G φ
  -- The latter is distinguished; transport along `(Tleft G).mapTriangle.mapIso e ≪≫ ι`.
  exact ⟨_, _, _, ⟨(Tleft G).mapTriangle.mapIso e ≪≫ ι⟩⟩
